From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.build_fme_model_input_revision_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function build -----*)

Definition build_safety_wit_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_initial_table)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH4 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> variables_pre)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_2 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (align4_3: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= UINT_MAX)) (PreH3 : ((0 < (N_initial_table * sizeof(UINT) )) -> (((0 < retval_6) /\ (retval_6 = (4 * align4_3 ))) /\ ((retval_6 + (((N_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= UINT_MAX)) (PreH6 : ((0 < (t_addr_cols * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= UINT_MAX)) (PreH9 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH10 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH11 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH12 : ((0 < M_initial_table) -> (0 < retval))) (PreH13 : (N_initial_table = variables_pre)) (PreH14 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH15 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH16 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH17 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH18 : (0 <= M_initial_table)) (PreH19 : (0 <= N_initial_table)) (PreH20 : (M_initial_table <= INT_MAX)) (PreH21 : (0 <= (M_initial_table * t_addr_cols ))) (PreH22 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH23 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH24 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH25 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH26 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH27 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH28 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH29 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  ((( &( "v" ) )) # UInt  |->_)
  **  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> retval_5)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> retval_6)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_3 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < v)) -> ((Znth (j) (prefix) (0)) = j))),
  ((( &( "v" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.undef_full rowPtr (M_initial_table + N_initial_table ) )
  **  (UIntArray.seg nbPtr 0 v prefix )
  **  (UIntArray.undef_seg nbPtr v N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_4 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (rowVals: (@list Z)) (v: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (PreH1 : (v >= t_addr_cols)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH7 : (0 <= v)) (PreH8 : (v <= (M_initial_table + N_initial_table ))) (PreH9 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (0 <= N_initial_table)) (PreH12 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH13 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < v)) -> ((Znth (j_2) (rowVals) (0)) = UINT_MAX))),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> head_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.seg rowPtr 0 v rowVals )
  **  (UIntArray.undef_seg rowPtr v (M_initial_table + N_initial_table ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_5 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_6 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((( &( "v" ) )) # UInt  |->_)
  **  (store_Z (cPtr + (r * sizeof( "__mpz_struct" ))) (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (store_Z q_coef (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr r 0 M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_7 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (v: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (0 <= v)) (PreH17 : (v < N_initial_table)) (PreH18 : (0 <= (r * t_addr_cols ))) (PreH19 : ((r * t_addr_cols ) <= INT_MAX)) (PreH20 : (0 <= (r * (M_initial_table + N_initial_table ) ))) (PreH21 : ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH22 : (q <> 0)) (PreH23 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH24 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH25 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH26 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "v" ) )) # UInt  |-> v)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.missing_i aPtr ((r * t_addr_cols ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z (aPtr + (((r * t_addr_cols ) + v ) * sizeof( "__mpz_struct" ))) 0 )
  **  (store_Z (q_coef + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_entail_wit_1 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_initial_table)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH4 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> 0)
  **  ((( &( "variables" ) )) # UInt  |-> variables_pre)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (t_addr_rows: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (0 <= t_addr_rows) ”
  &&  “ (t_addr_rows <= M_initial_table) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre head_pre (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_initial_table)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH4 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= M_initial_table) ”
  &&  (build_input_segment head_pre head_pre (N_initial_table + 1 ) (sublist (0) (0) (Rows_initial_table)) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) (sublist (0) (M_initial_table) (Rows_initial_table)) )
).

Definition build_entail_wit_1_split_goal_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_initial_table)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH4 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= M_initial_table) ”
.

Definition build_entail_wit_1_split_goal_spatial :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_initial_table)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH4 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  (build_input_segment head_pre head_pre (N_initial_table + 1 ) (sublist (0) (0) (Rows_initial_table)) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) (sublist (0) (M_initial_table) (Rows_initial_table)) )
.

Definition build_entail_wit_2 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q <> 0)),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  EX (coef: Z) (next: Z) (seen: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (0 <= seen) ”
  &&  “ (seen < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_initial_table) (seen))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (seen))))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> seen)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (seen)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (seen) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((seen + 1 )) (M_initial_table) (Rows_initial_table)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q <> 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (t_addr_rows)))) <> 0) ”
  &&  “ (t_addr_rows < M_initial_table) ”
  &&  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> (build_row_next ((build_row_at (Rows_initial_table) (t_addr_rows)))))
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at (Rows_initial_table) (t_addr_rows)))))
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_initial_table) (t_addr_rows)))) (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (t_addr_rows)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (t_addr_rows)))) 0 (N_initial_table + 1 ) (sublist ((t_addr_rows + 1 )) (M_initial_table) (Rows_initial_table)) )
).

Definition build_entail_wit_2_split_goal_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q <> 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (t_addr_rows)))) <> 0) ”
.

Definition build_entail_wit_2_split_goal_2 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q <> 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (t_addr_rows < M_initial_table) ”
.

Definition build_entail_wit_2_split_goal_spatial :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q <> 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> (build_row_next ((build_row_at (Rows_initial_table) (t_addr_rows)))))
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at (Rows_initial_table) (t_addr_rows)))))
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_initial_table) (t_addr_rows)))) (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (t_addr_rows)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (t_addr_rows)))) 0 (N_initial_table + 1 ) (sublist ((t_addr_rows + 1 )) (M_initial_table) (Rows_initial_table)) )
.

Definition build_entail_wit_3 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (seen: Z) (next: Z) (coef: Z) (q: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= seen)) (PreH4 : (seen < M_initial_table)) (PreH5 : (q <> 0)) (PreH6 : (next = (build_row_next ((build_row_at (Rows_initial_table) (seen)))))) (PreH7 : (coef <> 0)) (PreH8 : (coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (seen)))))) (PreH9 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH10 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> (unsigned_last_nbits ((seen + 1 )) (32)))
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (seen)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (seen) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((seen + 1 )) (M_initial_table) (Rows_initial_table)) )
|--
  EX (t_addr_rows: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (0 <= t_addr_rows) ”
  &&  “ (t_addr_rows <= M_initial_table) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre next (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (seen: Z) (next: Z) (coef: Z) (q: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= seen)) (PreH4 : (seen < M_initial_table)) (PreH5 : (q <> 0)) (PreH6 : (next = (build_row_next ((build_row_at (Rows_initial_table) (seen)))))) (PreH7 : (coef <> 0)) (PreH8 : (coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (seen)))))) (PreH9 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH10 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (seen)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (seen) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((seen + 1 )) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((unsigned_last_nbits ((seen + 1 )) (32)) <= M_initial_table) ”
  &&  “ (0 <= (unsigned_last_nbits ((seen + 1 )) (32))) ”
  &&  (build_input_segment head_pre next (N_initial_table + 1 ) (sublist (0) ((unsigned_last_nbits ((seen + 1 )) (32))) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((unsigned_last_nbits ((seen + 1 )) (32))) (M_initial_table) (Rows_initial_table)) )
).

Definition build_entail_wit_3_split_goal_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (seen: Z) (next: Z) (coef: Z) (q: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= seen)) (PreH4 : (seen < M_initial_table)) (PreH5 : (q <> 0)) (PreH6 : (next = (build_row_next ((build_row_at (Rows_initial_table) (seen)))))) (PreH7 : (coef <> 0)) (PreH8 : (coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (seen)))))) (PreH9 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH10 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (seen)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (seen) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((seen + 1 )) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((unsigned_last_nbits ((seen + 1 )) (32)) <= M_initial_table) ”
.

Definition build_entail_wit_3_split_goal_2 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (seen: Z) (next: Z) (coef: Z) (q: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= seen)) (PreH4 : (seen < M_initial_table)) (PreH5 : (q <> 0)) (PreH6 : (next = (build_row_next ((build_row_at (Rows_initial_table) (seen)))))) (PreH7 : (coef <> 0)) (PreH8 : (coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (seen)))))) (PreH9 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH10 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (seen)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (seen) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((seen + 1 )) (M_initial_table) (Rows_initial_table)) )
|--
  “ (0 <= (unsigned_last_nbits ((seen + 1 )) (32))) ”
.

Definition build_entail_wit_3_split_goal_spatial :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (seen: Z) (next: Z) (coef: Z) (q: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= seen)) (PreH4 : (seen < M_initial_table)) (PreH5 : (q <> 0)) (PreH6 : (next = (build_row_next ((build_row_at (Rows_initial_table) (seen)))))) (PreH7 : (coef <> 0)) (PreH8 : (coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (seen)))))) (PreH9 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH10 : ((0 < M_initial_table) -> (simplex_mpz_layout ))),
  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (seen)))) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (seen) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((seen + 1 )) (M_initial_table) (Rows_initial_table)) )
|--
  (build_input_segment head_pre next (N_initial_table + 1 ) (sublist (0) ((unsigned_last_nbits ((seen + 1 )) (32))) (Rows_initial_table)) )
  **  (build_input_segment next 0 (N_initial_table + 1 ) (sublist ((unsigned_last_nbits ((seen + 1 )) (32))) (M_initial_table) (Rows_initial_table)) )
.

Definition build_entail_wit_4 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> (unsigned_last_nbits ((N_initial_table + t_addr_rows )) (32)))
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  EX (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * (M_initial_table + N_initial_table ) )) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (t_addr_rows = M_initial_table) ”
  &&  “ ((unsigned_last_nbits ((N_initial_table + t_addr_rows )) (32)) = (M_initial_table + N_initial_table )) ”
  &&  “ ((unsigned_last_nbits ((N_initial_table + t_addr_rows )) (32)) = (M_initial_table + N_initial_table )) ”
  &&  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
).

Definition build_entail_wit_4_split_goal_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_2 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_3 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_4 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_5 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
.

Definition build_entail_wit_4_split_goal_6 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_7 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_8 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (0 <= (M_initial_table * (M_initial_table + N_initial_table ) )) ”
.

Definition build_entail_wit_4_split_goal_9 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (M_initial_table <= INT_MAX) ”
.

Definition build_entail_wit_4_split_goal_10 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (0 <= N_initial_table) ”
.

Definition build_entail_wit_4_split_goal_11 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ (t_addr_rows = M_initial_table) ”
.

Definition build_entail_wit_4_split_goal_12 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((unsigned_last_nbits ((N_initial_table + t_addr_rows )) (32)) = (M_initial_table + N_initial_table )) ”
.

Definition build_entail_wit_4_split_goal_13 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  “ ((unsigned_last_nbits ((N_initial_table + t_addr_rows )) (32)) = (M_initial_table + N_initial_table )) ”
.

Definition build_entail_wit_4_split_goal_spatial :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (t_addr_rows: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (0 <= t_addr_rows)) (PreH4 : (t_addr_rows <= M_initial_table)) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (t_addr_rows) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (t_addr_rows) (M_initial_table) (Rows_initial_table)) )
|--
  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_entail_wit_5 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols_2: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (align4_3: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= UINT_MAX)) (PreH3 : ((0 < (N_initial_table * sizeof(UINT) )) -> (((0 < retval_6) /\ (retval_6 = (4 * align4_3 ))) /\ ((retval_6 + (((N_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= UINT_MAX)) (PreH6 : ((0 < (t_addr_cols_2 * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols_2 * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= UINT_MAX)) (PreH9 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH10 : ((0 < (M_initial_table * t_addr_cols_2 )) -> (0 < retval_3))) (PreH11 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH12 : ((0 < M_initial_table) -> (0 < retval))) (PreH13 : (N_initial_table = variables_pre)) (PreH14 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH15 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH16 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH17 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH18 : (0 <= M_initial_table)) (PreH19 : (0 <= N_initial_table)) (PreH20 : (M_initial_table <= INT_MAX)) (PreH21 : (0 <= (M_initial_table * t_addr_cols_2 ))) (PreH22 : ((M_initial_table * t_addr_cols_2 ) <= INT_MAX)) (PreH23 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH24 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH25 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH26 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH27 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH28 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH29 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols_2 ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> retval_5)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> retval_6)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (prefix: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < 0)) -> ((Znth (j) (prefix) (0)) = j)) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.undef_full rowPtr (M_initial_table + N_initial_table ) )
  **  (UIntArray.seg nbPtr 0 0 prefix )
  **  (UIntArray.undef_seg nbPtr 0 N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols_2: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (align4_3: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= UINT_MAX)) (PreH3 : ((0 < (N_initial_table * sizeof(UINT) )) -> (((0 < retval_6) /\ (retval_6 = (4 * align4_3 ))) /\ ((retval_6 + (((N_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= UINT_MAX)) (PreH6 : ((0 < (t_addr_cols_2 * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols_2 * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= UINT_MAX)) (PreH9 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH10 : ((0 < (M_initial_table * t_addr_cols_2 )) -> (0 < retval_3))) (PreH11 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH12 : ((0 < M_initial_table) -> (0 < retval))) (PreH13 : (N_initial_table = variables_pre)) (PreH14 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH15 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH16 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH17 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH18 : (0 <= M_initial_table)) (PreH19 : (0 <= N_initial_table)) (PreH20 : (M_initial_table <= INT_MAX)) (PreH21 : (0 <= (M_initial_table * t_addr_cols_2 ))) (PreH22 : ((M_initial_table * t_addr_cols_2 ) <= INT_MAX)) (PreH23 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH24 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH25 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH26 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH27 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH28 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH29 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols_2 ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < 0)) -> ((Znth (j) ((@nil Z)) (0)) = j)) ”
  &&  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full retval_4 M_initial_table )
  **  (UIntArray.undef_full retval_5 (M_initial_table + N_initial_table ) )
  **  (UIntArray.undef_seg retval_6 0 N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
).

Definition build_entail_wit_5_split_goal_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols_2: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (align4_3: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= UINT_MAX)) (PreH3 : ((0 < (N_initial_table * sizeof(UINT) )) -> (((0 < retval_6) /\ (retval_6 = (4 * align4_3 ))) /\ ((retval_6 + (((N_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= UINT_MAX)) (PreH6 : ((0 < (t_addr_cols_2 * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols_2 * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= UINT_MAX)) (PreH9 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH10 : ((0 < (M_initial_table * t_addr_cols_2 )) -> (0 < retval_3))) (PreH11 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH12 : ((0 < M_initial_table) -> (0 < retval))) (PreH13 : (N_initial_table = variables_pre)) (PreH14 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH15 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH16 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH17 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH18 : (0 <= M_initial_table)) (PreH19 : (0 <= N_initial_table)) (PreH20 : (M_initial_table <= INT_MAX)) (PreH21 : (0 <= (M_initial_table * t_addr_cols_2 ))) (PreH22 : ((M_initial_table * t_addr_cols_2 ) <= INT_MAX)) (PreH23 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH24 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH25 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH26 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH27 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH28 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH29 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols_2 ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < 0)) -> ((Znth (j) ((@nil Z)) (0)) = j)) ”
.

Definition build_entail_wit_5_split_goal_spatial :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols_2: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (align4_3: Z) (retval_6: Z) (PreH1 : (0 <= retval_6)) (PreH2 : (retval_6 <= UINT_MAX)) (PreH3 : ((0 < (N_initial_table * sizeof(UINT) )) -> (((0 < retval_6) /\ (retval_6 = (4 * align4_3 ))) /\ ((retval_6 + (((N_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= UINT_MAX)) (PreH6 : ((0 < (t_addr_cols_2 * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols_2 * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= UINT_MAX)) (PreH9 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH10 : ((0 < (M_initial_table * t_addr_cols_2 )) -> (0 < retval_3))) (PreH11 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH12 : ((0 < M_initial_table) -> (0 < retval))) (PreH13 : (N_initial_table = variables_pre)) (PreH14 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH15 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH16 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH17 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH18 : (0 <= M_initial_table)) (PreH19 : (0 <= N_initial_table)) (PreH20 : (M_initial_table <= INT_MAX)) (PreH21 : (0 <= (M_initial_table * t_addr_cols_2 ))) (PreH22 : ((M_initial_table * t_addr_cols_2 ) <= INT_MAX)) (PreH23 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH24 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH25 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH26 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH27 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH28 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH29 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols_2 ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_5 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_6 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full retval_4 M_initial_table )
  **  (UIntArray.undef_full retval_5 (M_initial_table + N_initial_table ) )
  **  (UIntArray.undef_seg retval_6 0 N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_entail_wit_6 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (prefix_2: (@list Z)) (v: Z) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v < N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < v)) -> ((Znth (j) (prefix_2) (0)) = j))),
  (UIntArray.seg nbPtr_2 0 (v + 1 ) (app (prefix_2) ((cons (v) ((@nil Z))))) )
  **  (UIntArray.undef_seg nbPtr_2 (v + 1 ) N_initial_table )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr_2 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr_2 M_initial_table )
  **  (UIntArray.undef_full rowPtr_2 (M_initial_table + N_initial_table ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (prefix: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < (v + 1 ))) -> ((Znth (j) (prefix) (0)) = j)) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.undef_full rowPtr (M_initial_table + N_initial_table ) )
  **  (UIntArray.seg nbPtr 0 (v + 1 ) prefix )
  **  (UIntArray.undef_seg nbPtr (v + 1 ) N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_entail_wit_7 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr_2 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr_2 M_initial_table )
  **  (UIntArray.undef_full rowPtr_2 (M_initial_table + N_initial_table ) )
  **  (UIntArray.seg nbPtr_2 0 v prefix )
  **  (UIntArray.undef_seg nbPtr_2 v N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (rowVals: (@list Z)) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (M_initial_table + N_initial_table )) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth (j_2) (rowVals) (0)) = UINT_MAX)) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.seg rowPtr 0 0 rowVals )
  **  (UIntArray.undef_seg rowPtr 0 (M_initial_table + N_initial_table ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  TT && emp 
|--
  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth (j_2) ((@nil Z)) (0)) = UINT_MAX)) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ (0 <= (M_initial_table + N_initial_table )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < variables_pre)) -> ((Znth (j) (prefix) (0)) = j)) ”
  &&  emp
).

Definition build_entail_wit_7_split_goal_1 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  forall (j_2: Z), (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth (j_2) ((@nil Z)) (0)) = UINT_MAX))
.

Definition build_entail_wit_7_split_goal_2 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)
.

Definition build_entail_wit_7_split_goal_3 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  (0 <= M_initial_table)
.

Definition build_entail_wit_7_split_goal_4 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  ((M_initial_table + N_initial_table ) < UINT_MAX)
.

Definition build_entail_wit_7_split_goal_5 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  (0 <= (M_initial_table + N_initial_table ))
.

Definition build_entail_wit_7_split_goal_6 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (prefix) (0)) = j_3))),
  forall (j: Z), (((0 <= j) /\ (j < variables_pre)) -> ((Znth (j) (prefix) (0)) = j))
.

Definition build_entail_wit_8 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (rowVals_2: (@list Z)) (v: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v < t_addr_cols_2)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j))) (PreH7 : (0 <= v)) (PreH8 : (v <= (M_initial_table + N_initial_table ))) (PreH9 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (0 <= N_initial_table)) (PreH12 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH13 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < v)) -> ((Znth (j_2) (rowVals_2) (0)) = UINT_MAX))),
  (UIntArray.seg rowPtr_2 0 (v + 1 ) (app (rowVals_2) ((cons (UINT_MAX) ((@nil Z))))) )
  **  (UIntArray.undef_seg rowPtr_2 (v + 1 ) (M_initial_table + N_initial_table ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr_2 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr_2 M_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (rowVals: (@list Z)) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= (M_initial_table + N_initial_table )) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < (v + 1 ))) -> ((Znth (j_2) (rowVals) (0)) = UINT_MAX)) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.seg rowPtr 0 (v + 1 ) rowVals )
  **  (UIntArray.undef_seg rowPtr (v + 1 ) (M_initial_table + N_initial_table ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_entail_wit_9 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (rowVals_2: (@list Z)) (v: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v >= t_addr_cols_2)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= v)) (PreH8 : (v <= (M_initial_table + N_initial_table ))) (PreH9 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (0 <= N_initial_table)) (PreH12 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH13 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH14 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (rowVals_2) (0)) = UINT_MAX))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr_2 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr_2 M_initial_table )
  **  (UIntArray.seg rowPtr_2 0 v rowVals_2 )
  **  (UIntArray.undef_seg rowPtr_2 v (M_initial_table + N_initial_table ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) 0 0 0 (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (UIntArray.seg bPtr 0 0 bVals )
  **  (UIntArray.undef_seg bPtr 0 M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre head_pre (N_initial_table + 1 ) (sublist (0) (0) (Rows_initial_table)) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) (sublist (0) (M_initial_table) (Rows_initial_table)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (rowVals_2: (@list Z)) (v: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v >= t_addr_cols_2)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= v)) (PreH8 : (v <= (M_initial_table + N_initial_table ))) (PreH9 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (0 <= N_initial_table)) (PreH12 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH13 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH14 : forall (j_3: Z), (((0 <= j_3) /\ (j_3 < v)) -> ((Znth (j_3) (rowVals_2) (0)) = UINT_MAX))),
  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr_2 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) 0 0 0 (build_matrix (Rows_initial_table)) dVals cVals aVals (@nil Z) rowVals_2 ) ”
  &&  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (build_input_segment head_pre head_pre (N_initial_table + 1 ) (sublist (0) (0) (Rows_initial_table)) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) (sublist (0) (M_initial_table) (Rows_initial_table)) )
).

Definition build_entail_wit_10 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (r < M_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
  **  (UIntArray.seg bPtr_2 0 r bVals_2 )
  **  (UIntArray.undef_seg bPtr_2 r M_initial_table )
  **  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) rowVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (r) (M_initial_table) (Rows_initial_table)) )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (r < M_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (r) (M_initial_table) (Rows_initial_table)) )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 rowVals_2 ) ”
  &&  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> (build_row_next ((build_row_at (Rows_initial_table) (r)))))
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr_2 r 0 M_initial_table dVals )
  **  (store_Z (dPtr_2 + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
).

Definition build_entail_wit_11 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (nbVals_2: (@list Z)) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (t_addr_cols_2: Z) (r: Z) (q: Z) (q_coef_2: Z) (q_next_2: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (store_Z (dPtr_2 + (r * sizeof( "__mpz_struct" ))) 1 )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef_2)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr_2 0 r bVals_2 )
  **  (UIntArray.undef_seg bPtr_2 r M_initial_table )
  **  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) rowVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef_2 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr_2 r 0 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr r 0 M_initial_table cVals )
  **  (store_Z (cPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z q_coef (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (nbVals_2: (@list Z)) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (t_addr_cols_2: Z) (r: Z) (q: Z) (q_coef_2: Z) (q_next_2: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (store_Z (dPtr_2 + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef_2 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr_2 r 0 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 rowVals_2 ) ”
  &&  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr_2 r 0 M_initial_table dVals )
  **  (store_Z (dPtr_2 + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr_2 r 0 M_initial_table cVals )
  **  (store_Z (cPtr_2 + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
).

Definition build_entail_wit_12 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (nbVals_2: (@list Z)) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (t_addr_cols_2: Z) (r: Z) (q: Z) (q_coef_2: Z) (q_next_2: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (store_Z (cPtr_2 + (r * sizeof( "__mpz_struct" ))) (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (store_Z q_coef_2 (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef_2)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr_2 0 r bVals_2 )
  **  (UIntArray.undef_seg bPtr_2 r M_initial_table )
  **  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) rowVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef_2 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr_2 r 0 M_initial_table dVals_2 )
  **  (store_Z (dPtr_2 + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr_2 r 0 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (nbVals_2: (@list Z)) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (t_addr_cols_2: Z) (r: Z) (q: Z) (q_coef_2: Z) (q_next_2: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (store_Z (cPtr_2 + (r * sizeof( "__mpz_struct" ))) (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (store_Z q_coef_2 (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef_2 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr_2 r 0 M_initial_table dVals_2 )
  **  (store_Z (dPtr_2 + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr_2 r 0 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 rowVals_2 ) ”
  &&  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
).

Definition build_entail_wit_13 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (q_next_2: Z) (q_coef_2: Z) (q: Z) (v: Z) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v < N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (r < M_initial_table)) (PreH17 : (0 <= v)) (PreH18 : (v <= N_initial_table)) (PreH19 : (q <> 0)) (PreH20 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH21 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH22 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH23 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef_2)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr_2 0 r bVals_2 )
  **  (UIntArray.undef_seg bPtr_2 r M_initial_table )
  **  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) rowVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef_2 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= v) ”
  &&  “ (v < N_initial_table) ”
  &&  “ (0 <= (r * t_addr_cols )) ”
  &&  “ ((r * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (r * (M_initial_table + N_initial_table ) )) ”
  &&  “ ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.missing_i aPtr ((r * t_addr_cols ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z (aPtr + (((r * t_addr_cols ) + v ) * sizeof( "__mpz_struct" ))) 0 )
  **  (store_Z (q_coef + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (q_next_2: Z) (q_coef_2: Z) (q: Z) (v: Z) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v < N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (r < M_initial_table)) (PreH17 : (0 <= v)) (PreH18 : (v <= N_initial_table)) (PreH19 : (q <> 0)) (PreH20 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH21 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH22 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH23 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef_2 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= v) ”
  &&  “ (v < N_initial_table) ”
  &&  “ (0 <= (r * (M_initial_table + N_initial_table ) )) ”
  &&  “ ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ (0 <= (r * (M_initial_table + N_initial_table ) )) ”
  &&  “ ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ (q <> 0) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 rowVals_2 ) ”
  &&  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (MpzArray.missing_i aPtr_2 ((r * (M_initial_table + N_initial_table ) ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z (aPtr_2 + (((r * (M_initial_table + N_initial_table ) ) + v ) * sizeof( "__mpz_struct" ))) 0 )
  **  (store_Z ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
).

Definition build_entail_wit_14 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (nbVals_2: (@list Z)) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (t_addr_cols_2: Z) (r: Z) (v: Z) (q: Z) (q_coef_2: Z) (q_next_2: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (0 <= v)) (PreH17 : (v < N_initial_table)) (PreH18 : (0 <= (r * t_addr_cols_2 ))) (PreH19 : ((r * t_addr_cols_2 ) <= INT_MAX)) (PreH20 : (0 <= (r * (M_initial_table + N_initial_table ) ))) (PreH21 : ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH22 : (q <> 0)) (PreH23 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH24 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH25 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH26 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (store_Z (aPtr_2 + (((r * t_addr_cols_2 ) + v ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (store_Z (q_coef_2 + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef_2)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next_2)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr_2 0 r bVals_2 )
  **  (UIntArray.undef_seg bPtr_2 r M_initial_table )
  **  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) rowVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef_2 (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.missing_i aPtr_2 ((r * t_addr_cols_2 ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= N_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r (v + 1 ) (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (nbVals_2: (@list Z)) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (t_addr_cols_2: Z) (r: Z) (v: Z) (q: Z) (q_coef_2: Z) (q_next_2: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (0 <= v)) (PreH17 : (v < N_initial_table)) (PreH18 : (0 <= (r * t_addr_cols_2 ))) (PreH19 : ((r * t_addr_cols_2 ) <= INT_MAX)) (PreH20 : (0 <= (r * (M_initial_table + N_initial_table ) ))) (PreH21 : ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH22 : (q <> 0)) (PreH23 : (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH24 : (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH25 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH26 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (store_Z (aPtr_2 + (((r * t_addr_cols_2 ) + v ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (store_Z (q_coef_2 + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef_2 (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.missing_i aPtr_2 ((r * t_addr_cols_2 ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (q_next_2 = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_coef_2 = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= (v + 1 )) ”
  &&  “ ((v + 1 ) <= N_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r (v + 1 ) (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 rowVals_2 ) ”
  &&  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
).

Definition build_entail_wit_15 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (q_next: Z) (q_coef: Z) (q: Z) (v: Z) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (r < M_initial_table)) (PreH17 : (0 <= v)) (PreH18 : (v <= N_initial_table)) (PreH19 : (q <> 0)) (PreH20 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH21 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH22 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH23 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) (replace_Znth ((N_initial_table + r )) (r) (rowVals_2)) )
  **  (UIntArray.seg bPtr_2 0 (r + 1 ) (app (bVals_2) ((cons ((N_initial_table + r )) ((@nil Z))))) )
  **  (UIntArray.undef_seg bPtr_2 (r + 1 ) M_initial_table )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z),
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) (r + 1 ) 0 (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (UIntArray.seg bPtr 0 (r + 1 ) bVals )
  **  (UIntArray.undef_seg bPtr (r + 1 ) M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q_next (N_initial_table + 1 ) (sublist (0) ((r + 1 )) (Rows_initial_table)) )
  **  (build_input_segment q_next 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (q_next: Z) (q_coef: Z) (q: Z) (v: Z) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols_2: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols_2 = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (r < M_initial_table)) (PreH17 : (0 <= v)) (PreH18 : (v <= N_initial_table)) (PreH19 : (q <> 0)) (PreH20 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH21 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH22 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH23 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (t_addr_cols_2 = (M_initial_table + N_initial_table )) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (0 <= (r + 1 )) ”
  &&  “ ((r + 1 ) <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) (r + 1 ) 0 (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals (app (bVals_2) ((cons ((N_initial_table + r )) ((@nil Z))))) (replace_Znth ((N_initial_table + r )) (r) (rowVals_2)) ) ”
  &&  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (build_input_segment head_pre q_next (N_initial_table + 1 ) (sublist (0) ((r + 1 )) (Rows_initial_table)) )
  **  (build_input_segment q_next 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
).

Definition build_return_wit_1 :=
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols: Z) (record_return: Z) (PreH1 : (r >= M_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  ((&((record_return)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&((record_return)  # "table" ->ₛ "rows")) # UInt  |-> M_initial_table)
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_initial_table nbVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
  **  (UIntArray.seg bPtr_2 0 r bVals_2 )
  **  (UIntArray.full rowPtr_2 (M_initial_table + N_initial_table ) rowVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (r) (M_initial_table) (Rows_initial_table)) )
|--
  EX (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (retval_cols: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (simplex_initial_table N_initial_table M_initial_table (M_initial_table + N_initial_table ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_initial_table M_initial_table (M_initial_table + N_initial_table ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals ) ”
  &&  “ (retval_cols = (M_initial_table + N_initial_table )) ”
  &&  ((&((record_return)  # "table" ->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&((record_return)  # "table" ->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&((record_return)  # "table" ->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&((record_return)  # "table" ->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&((record_return)  # "table" ->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&((record_return)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&((record_return)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&((record_return)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full bPtr M_initial_table bVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
) \/
(
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (r: Z) (nbVals_2: (@list Z)) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (t_addr_cols: Z) (PreH1 : (r >= M_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < N_initial_table)) -> ((Znth (j_2) (nbVals_2) (0)) = j_2))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )),
  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals_2 )
  **  (MpzArray.full cPtr_2 M_initial_table cVals_2 )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals_2 )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (r) (M_initial_table) (Rows_initial_table)) )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)),
  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (simplex_initial_table N_initial_table M_initial_table (M_initial_table + N_initial_table ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 rowVals_2 ) ”
  &&  “ (simplex_initial_equations N_initial_table M_initial_table (M_initial_table + N_initial_table ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals_2 ) ”
  &&  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
  **  (simplex_malloc_token dPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 M_initial_table dVals )
  **  (simplex_malloc_token cPtr_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 M_initial_table cVals )
  **  (simplex_malloc_token aPtr_2 ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (simplex_malloc_token bPtr_2 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr_2 (N_initial_table * sizeof(UINT) ) )
).

Definition build_partial_solve_wit_1_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH6 : (0 <= M_initial_table)) (PreH7 : (0 <= N_initial_table)) (PreH8 : (M_initial_table <= INT_MAX)) (PreH9 : (0 <= (M_initial_table * t_addr_cols ))) (PreH10 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH11 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH12 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH13 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH14 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH15 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH16 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH17 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition build_partial_solve_wit_1_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH6 : (0 <= M_initial_table)) (PreH7 : (0 <= N_initial_table)) (PreH8 : (M_initial_table <= INT_MAX)) (PreH9 : (0 <= (M_initial_table * t_addr_cols ))) (PreH10 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH11 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH12 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH13 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH14 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH15 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH16 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH17 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_1 := build_partial_solve_wit_1_pure -> build_partial_solve_wit_1_aux.

Definition build_partial_solve_wit_2_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (PreH1 : ((0 < M_initial_table) -> (0 < retval))) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (M_initial_table <= INT_MAX)) (PreH10 : (0 <= (M_initial_table * t_addr_cols ))) (PreH11 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH12 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH13 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH14 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH15 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH16 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH17 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH18 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition build_partial_solve_wit_2_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (PreH1 : ((0 < M_initial_table) -> (0 < retval))) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (M_initial_table <= INT_MAX)) (PreH10 : (0 <= (M_initial_table * t_addr_cols ))) (PreH11 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH12 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH13 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH14 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH15 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH16 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH17 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH18 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval)) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_2 := build_partial_solve_wit_2_pure -> build_partial_solve_wit_2_aux.

Definition build_partial_solve_wit_3_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (PreH1 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH2 : ((0 < M_initial_table) -> (0 < retval))) (PreH3 : (N_initial_table = variables_pre)) (PreH4 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH5 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH6 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH7 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH8 : (0 <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (M_initial_table <= INT_MAX)) (PreH11 : (0 <= (M_initial_table * t_addr_cols ))) (PreH12 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH13 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH14 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH15 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH16 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH17 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH18 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH19 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ ((0 < (M_initial_table * t_addr_cols )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition build_partial_solve_wit_3_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (PreH1 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH2 : ((0 < M_initial_table) -> (0 < retval))) (PreH3 : (N_initial_table = variables_pre)) (PreH4 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH5 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH6 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH7 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH8 : (0 <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (M_initial_table <= INT_MAX)) (PreH11 : (0 <= (M_initial_table * t_addr_cols ))) (PreH12 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH13 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH14 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH15 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH16 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH17 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH18 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH19 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ ((0 < (M_initial_table * t_addr_cols )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval_2)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval)) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_3 := build_partial_solve_wit_3_pure -> build_partial_solve_wit_3_aux.

Definition build_partial_solve_wit_4_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH2 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH3 : ((0 < M_initial_table) -> (0 < retval))) (PreH4 : (N_initial_table = variables_pre)) (PreH5 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH6 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH7 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH8 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH9 : (0 <= M_initial_table)) (PreH10 : (0 <= N_initial_table)) (PreH11 : (M_initial_table <= INT_MAX)) (PreH12 : (0 <= (M_initial_table * t_addr_cols ))) (PreH13 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH14 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH15 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH16 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH17 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH18 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH19 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH20 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (M_initial_table * sizeof(UINT) )) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
.

Definition build_partial_solve_wit_4_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH2 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH3 : ((0 < M_initial_table) -> (0 < retval))) (PreH4 : (N_initial_table = variables_pre)) (PreH5 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH6 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH7 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH8 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH9 : (0 <= M_initial_table)) (PreH10 : (0 <= N_initial_table)) (PreH11 : (M_initial_table <= INT_MAX)) (PreH12 : (0 <= (M_initial_table * t_addr_cols ))) (PreH13 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH14 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH15 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH16 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH17 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH18 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH19 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH20 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (M_initial_table * sizeof(UINT) )) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval_2)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval)) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_4 := build_partial_solve_wit_4_pure -> build_partial_solve_wit_4_aux.

Definition build_partial_solve_wit_5_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= UINT_MAX)) (PreH3 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH5 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH6 : ((0 < M_initial_table) -> (0 < retval))) (PreH7 : (N_initial_table = variables_pre)) (PreH8 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH9 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH10 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH11 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH12 : (0 <= M_initial_table)) (PreH13 : (0 <= N_initial_table)) (PreH14 : (M_initial_table <= INT_MAX)) (PreH15 : (0 <= (M_initial_table * t_addr_cols ))) (PreH16 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH17 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH18 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH19 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH20 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH21 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH22 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH23 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (t_addr_cols * sizeof(UINT) )) ”
  &&  “ ((t_addr_cols * sizeof(UINT) ) <= INT_MAX) ”
.

Definition build_partial_solve_wit_5_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= UINT_MAX)) (PreH3 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH5 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH6 : ((0 < M_initial_table) -> (0 < retval))) (PreH7 : (N_initial_table = variables_pre)) (PreH8 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH9 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH10 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH11 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH12 : (0 <= M_initial_table)) (PreH13 : (0 <= N_initial_table)) (PreH14 : (M_initial_table <= INT_MAX)) (PreH15 : (0 <= (M_initial_table * t_addr_cols ))) (PreH16 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH17 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH18 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH19 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH20 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH21 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH22 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH23 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (t_addr_cols * sizeof(UINT) )) ”
  &&  “ ((t_addr_cols * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (0 <= retval_4) ”
  &&  “ (retval_4 <= UINT_MAX) ”
  &&  “ ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX))) ”
  &&  “ ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval_2)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval)) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_5 := build_partial_solve_wit_5_pure -> build_partial_solve_wit_5_aux.

Definition build_partial_solve_wit_6_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= UINT_MAX)) (PreH3 : ((0 < (t_addr_cols * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= UINT_MAX)) (PreH6 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH8 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH9 : ((0 < M_initial_table) -> (0 < retval))) (PreH10 : (N_initial_table = variables_pre)) (PreH11 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH12 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH13 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (0 <= M_initial_table)) (PreH16 : (0 <= N_initial_table)) (PreH17 : (M_initial_table <= INT_MAX)) (PreH18 : (0 <= (M_initial_table * t_addr_cols ))) (PreH19 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH20 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH21 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH22 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH23 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH24 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH25 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH26 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> retval_5)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (N_initial_table * sizeof(UINT) )) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
.

Definition build_partial_solve_wit_6_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (t_addr_cols: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (align4: Z) (retval_4: Z) (align4_2: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= UINT_MAX)) (PreH3 : ((0 < (t_addr_cols * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= UINT_MAX)) (PreH6 : ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH7 : ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3))) (PreH8 : ((0 < M_initial_table) -> (0 < retval_2))) (PreH9 : ((0 < M_initial_table) -> (0 < retval))) (PreH10 : (N_initial_table = variables_pre)) (PreH11 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH12 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH13 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (0 <= M_initial_table)) (PreH16 : (0 <= N_initial_table)) (PreH17 : (M_initial_table <= INT_MAX)) (PreH18 : (0 <= (M_initial_table * t_addr_cols ))) (PreH19 : ((M_initial_table * t_addr_cols ) <= INT_MAX)) (PreH20 : (0 <= (M_initial_table * sizeof( "__mpz_struct" ) ))) (PreH21 : ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH22 : (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH23 : (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH24 : ((M_initial_table * sizeof(UINT) ) <= INT_MAX)) (PreH25 : (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH26 : ((N_initial_table * sizeof(UINT) ) <= INT_MAX)),
  (simplex_malloc_token retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> retval_5)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (0 <= (N_initial_table * sizeof(UINT) )) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (0 <= retval_5) ”
  &&  “ (retval_5 <= UINT_MAX) ”
  &&  “ ((0 < (t_addr_cols * sizeof(UINT) )) -> (((0 < retval_5) /\ (retval_5 = (4 * align4_2 ))) /\ ((retval_5 + (((t_addr_cols * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX))) ”
  &&  “ (0 <= retval_4) ”
  &&  “ (retval_4 <= UINT_MAX) ”
  &&  “ ((0 < (M_initial_table * sizeof(UINT) )) -> (((0 < retval_4) /\ (retval_4 = (4 * align4 ))) /\ ((retval_4 + (((M_initial_table * sizeof(UINT) ) + (-1) ) * 1)) <= UINT_MAX))) ”
  &&  “ ((0 < (M_initial_table * t_addr_cols )) -> (0 < retval_3)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval_2)) ”
  &&  “ ((0 < M_initial_table) -> (0 < retval)) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (M_initial_table <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * t_addr_cols )) ”
  &&  “ ((M_initial_table * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (M_initial_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_initial_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((M_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((M_initial_table + N_initial_table ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((N_initial_table * sizeof(UINT) ) <= INT_MAX) ”
  &&  (simplex_malloc_token retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_5 (t_addr_cols * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full retval_4 (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token retval_3 ((M_initial_table * t_addr_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_3 0 (M_initial_table * t_addr_cols ) ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval_2 (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval_2 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_malloc_token retval (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_mpz_dummy_seg retval 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> retval)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> retval_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> retval_3)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> retval_4)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> retval_5)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_6 := build_partial_solve_wit_6_pure -> build_partial_solve_wit_6_aux.

Definition build_partial_solve_wit_7 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (prefix: (@list Z)) (v: Z) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (PreH1 : (v < N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH7 : (0 <= v)) (PreH8 : (v <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : forall (j: Z), (((0 <= j) /\ (j < v)) -> ((Znth (j) (prefix) (0)) = j))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.undef_full rowPtr (M_initial_table + N_initial_table ) )
  **  (UIntArray.seg nbPtr 0 v prefix )
  **  (UIntArray.undef_seg nbPtr v N_initial_table )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (v < N_initial_table) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < v)) -> ((Znth (j) (prefix) (0)) = j)) ”
  &&  (((nbPtr + (v * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg nbPtr (v + 1 ) N_initial_table )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.undef_full rowPtr (M_initial_table + N_initial_table ) )
  **  (UIntArray.seg nbPtr 0 v prefix )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_8 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (rowVals: (@list Z)) (v: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (PreH1 : (v < t_addr_cols)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH7 : (0 <= v)) (PreH8 : (v <= (M_initial_table + N_initial_table ))) (PreH9 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (0 <= N_initial_table)) (PreH12 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH13 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH14 : forall (j_2: Z), (((0 <= j_2) /\ (j_2 < v)) -> ((Znth (j_2) (rowVals) (0)) = UINT_MAX))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.seg rowPtr 0 v rowVals )
  **  (UIntArray.undef_seg rowPtr v (M_initial_table + N_initial_table ) )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
|--
  “ (v < t_addr_cols) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= (M_initial_table + N_initial_table )) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ forall (j_2: Z), (((0 <= j_2) /\ (j_2 < v)) -> ((Znth (j_2) (rowVals) (0)) = UINT_MAX)) ”
  &&  (((rowPtr + (v * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rowPtr (v + 1 ) (M_initial_table + N_initial_table ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (simplex_mpz_dummy_seg dPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg cPtr 0 M_initial_table ( &( "mpz_dummy_limb" ) ) )
  **  (simplex_mpz_dummy_seg aPtr 0 (M_initial_table * (M_initial_table + N_initial_table ) ) ( &( "mpz_dummy_limb" ) ) )
  **  (UIntArray.undef_full bPtr M_initial_table )
  **  (UIntArray.seg rowPtr 0 v rowVals )
  **  (build_input_segment head_pre 0 (N_initial_table + 1 ) Rows_initial_table )
.

Definition build_partial_solve_wit_9_pure :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_initial_table)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
|--
  “ (1 = 1) ”
  &&  “ (0 <= 1) ”
.

Definition build_partial_solve_wit_9_aux :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
|--
  “ (1 = 1) ”
  &&  “ (0 <= 1) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
.

Definition build_partial_solve_wit_9 := build_partial_solve_wit_9_pure -> build_partial_solve_wit_9_aux.

Definition build_partial_solve_wit_10 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (q <> 0)) (PreH17 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH18 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH19 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH20 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr r 0 M_initial_table cVals )
  **  (store_Z (cPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z q_coef (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
|--
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  (store_Z (cPtr + (r * sizeof( "__mpz_struct" ))) 0 )
  **  (store_Z q_coef (Znth (0) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef 0 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.missing_i dPtr r 0 M_initial_table dVals )
  **  (store_Z (dPtr + (r * sizeof( "__mpz_struct" ))) 1 )
  **  (MpzArray.missing_i cPtr r 0 M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
.

Definition build_partial_solve_wit_11 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (nbVals: (@list Z)) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (t_addr_cols: Z) (r: Z) (v: Z) (q: Z) (q_coef: Z) (q_next: Z) (PreH1 : (N_initial_table = variables_pre)) (PreH2 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH3 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH4 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH5 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH6 : (0 <= r)) (PreH7 : (r <= M_initial_table)) (PreH8 : (0 <= N_initial_table)) (PreH9 : (N_initial_table < UINT_MAX)) (PreH10 : (0 <= M_initial_table)) (PreH11 : (M_initial_table < UINT_MAX)) (PreH12 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH13 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH14 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH15 : (r < M_initial_table)) (PreH16 : (0 <= v)) (PreH17 : (v < N_initial_table)) (PreH18 : (0 <= (r * t_addr_cols ))) (PreH19 : ((r * t_addr_cols ) <= INT_MAX)) (PreH20 : (0 <= (r * (M_initial_table + N_initial_table ) ))) (PreH21 : ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH22 : (q <> 0)) (PreH23 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH24 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH25 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH26 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.missing_i aPtr ((r * t_addr_cols ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (store_Z (aPtr + (((r * t_addr_cols ) + v ) * sizeof( "__mpz_struct" ))) 0 )
  **  (store_Z (q_coef + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
|--
  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= v) ”
  &&  “ (v < N_initial_table) ”
  &&  “ (0 <= (r * t_addr_cols )) ”
  &&  “ ((r * t_addr_cols ) <= INT_MAX) ”
  &&  “ (0 <= (r * (M_initial_table + N_initial_table ) )) ”
  &&  “ ((r * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  (store_Z (aPtr + (((r * t_addr_cols ) + v ) * sizeof( "__mpz_struct" ))) 0 )
  **  (store_Z (q_coef + ((v + 1 ) * sizeof( "__mpz_struct" ))) (Znth ((v + 1 )) ((build_row_entries ((build_row_at (Rows_initial_table) (r))))) (0)) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.missing_i q_coef (v + 1 ) 0 (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.missing_i aPtr ((r * t_addr_cols ) + v ) 0 (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
.

Definition build_partial_solve_wit_12 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (q: Z) (v: Z) (r: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (r < M_initial_table)) (PreH17 : (0 <= v)) (PreH18 : (v <= N_initial_table)) (PreH19 : (q <> 0)) (PreH20 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH21 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH22 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH23 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
|--
  “ (v >= N_initial_table) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= N_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  (((bPtr + (r * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg bPtr (r + 1 ) M_initial_table )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
.

Definition build_partial_solve_wit_13 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (q_next: Z) (q_coef: Z) (q: Z) (v: Z) (r: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (PreH1 : (v >= N_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (r < M_initial_table)) (PreH17 : (0 <= v)) (PreH18 : (v <= N_initial_table)) (PreH19 : (q <> 0)) (PreH20 : (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r)))))) (PreH21 : (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r)))))) (PreH22 : ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0)) (PreH23 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  (UIntArray.seg bPtr 0 (r + 1 ) (app (bVals) ((cons ((N_initial_table + r )) ((@nil Z))))) )
  **  (UIntArray.undef_seg bPtr (r + 1 ) M_initial_table )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
|--
  “ (v >= N_initial_table) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (r < M_initial_table) ”
  &&  “ (0 <= v) ”
  &&  “ (v <= N_initial_table) ”
  &&  “ (q <> 0) ”
  &&  “ (q_coef = (build_row_coefficients ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ (q_next = (build_row_next ((build_row_at (Rows_initial_table) (r))))) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_initial_table) (r)))) <> 0) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r v (r + 1 ) (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
  &&  (((rowPtr + ((N_initial_table + r ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rowPtr (N_initial_table + r ) 0 (M_initial_table + N_initial_table ) rowVals )
  **  (UIntArray.seg bPtr 0 (r + 1 ) (app (bVals) ((cons ((N_initial_table + r )) ((@nil Z))))) )
  **  (UIntArray.undef_seg bPtr (r + 1 ) M_initial_table )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_initial_table) (r)))) 0 (N_initial_table + 1 ) (sublist ((r + 1 )) (M_initial_table) (Rows_initial_table)) )
  **  (MpzArray.full q_coef (N_initial_table + 1 ) (build_row_entries ((build_row_at (Rows_initial_table) (r)))) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
.

Definition build_partial_solve_wit_14 :=
forall (Rows_initial_table: (@list build_row_snapshot)) (M_initial_table: Z) (N_initial_table: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (r: Z) (nbVals: (@list Z)) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (record_return: Z) (PreH1 : (r >= M_initial_table)) (PreH2 : (N_initial_table = variables_pre)) (PreH3 : (M_initial_table = (Zlength (Rows_initial_table)))) (PreH4 : (t_addr_cols = (M_initial_table + N_initial_table ))) (PreH5 : (simplex_dimensions_ok M_initial_table N_initial_table )) (PreH6 : forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH7 : (0 <= r)) (PreH8 : (r <= M_initial_table)) (PreH9 : (0 <= N_initial_table)) (PreH10 : (N_initial_table < UINT_MAX)) (PreH11 : (0 <= M_initial_table)) (PreH12 : (M_initial_table < UINT_MAX)) (PreH13 : ((M_initial_table + N_initial_table ) < UINT_MAX)) (PreH14 : ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX)) (PreH15 : ((0 < M_initial_table) -> (simplex_mpz_layout ))) (PreH16 : (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals )),
  (UndefStructPredtable record_return )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.undef_seg bPtr r M_initial_table )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (r) (M_initial_table) (Rows_initial_table)) )
|--
  “ (r >= M_initial_table) ”
  &&  “ (N_initial_table = variables_pre) ”
  &&  “ (M_initial_table = (Zlength (Rows_initial_table))) ”
  &&  “ (t_addr_cols = (M_initial_table + N_initial_table )) ”
  &&  “ (simplex_dimensions_ok M_initial_table N_initial_table ) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_initial_table)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= M_initial_table) ”
  &&  “ (0 <= N_initial_table) ”
  &&  “ (N_initial_table < UINT_MAX) ”
  &&  “ (0 <= M_initial_table) ”
  &&  “ (M_initial_table < UINT_MAX) ”
  &&  “ ((M_initial_table + N_initial_table ) < UINT_MAX) ”
  &&  “ ((M_initial_table * (M_initial_table + N_initial_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_initial_table) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_build_prefix N_initial_table (M_initial_table + N_initial_table ) r 0 r (build_matrix (Rows_initial_table)) dVals cVals aVals bVals rowVals ) ”
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
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_initial_table)
  **  (simplex_malloc_token dPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token cPtr (M_initial_table * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token aPtr ((M_initial_table * (M_initial_table + N_initial_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token bPtr (M_initial_table * sizeof(UINT) ) )
  **  (simplex_malloc_token nbPtr (N_initial_table * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_initial_table nbVals )
  **  (simplex_malloc_token rowPtr ((M_initial_table + N_initial_table ) * sizeof(UINT) ) )
  **  (MpzArray.full dPtr M_initial_table dVals )
  **  (MpzArray.full cPtr M_initial_table cVals )
  **  (MpzArray.full aPtr (M_initial_table * (M_initial_table + N_initial_table ) ) aVals )
  **  (UIntArray.seg bPtr 0 r bVals )
  **  (UIntArray.full rowPtr (M_initial_table + N_initial_table ) rowVals )
  **  (build_input_segment head_pre q (N_initial_table + 1 ) (sublist (0) (r) (Rows_initial_table)) )
  **  (build_input_segment q 0 (N_initial_table + 1 ) (sublist (r) (M_initial_table) (Rows_initial_table)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_safety_wit_3 : build_safety_wit_3.
Axiom proof_of_build_safety_wit_4 : build_safety_wit_4.
Axiom proof_of_build_safety_wit_5 : build_safety_wit_5.
Axiom proof_of_build_safety_wit_6 : build_safety_wit_6.
Axiom proof_of_build_safety_wit_7 : build_safety_wit_7.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2 : build_entail_wit_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_entail_wit_4 : build_entail_wit_4.
Axiom proof_of_build_entail_wit_5 : build_entail_wit_5.
Axiom proof_of_build_entail_wit_6 : build_entail_wit_6.
Axiom proof_of_build_entail_wit_7 : build_entail_wit_7.
Axiom proof_of_build_entail_wit_8 : build_entail_wit_8.
Axiom proof_of_build_entail_wit_9 : build_entail_wit_9.
Axiom proof_of_build_entail_wit_10 : build_entail_wit_10.
Axiom proof_of_build_entail_wit_11 : build_entail_wit_11.
Axiom proof_of_build_entail_wit_12 : build_entail_wit_12.
Axiom proof_of_build_entail_wit_13 : build_entail_wit_13.
Axiom proof_of_build_entail_wit_14 : build_entail_wit_14.
Axiom proof_of_build_entail_wit_15 : build_entail_wit_15.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_partial_solve_wit_1_pure : build_partial_solve_wit_1_pure.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2_pure : build_partial_solve_wit_2_pure.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.
Axiom proof_of_build_partial_solve_wit_3_pure : build_partial_solve_wit_3_pure.
Axiom proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3.
Axiom proof_of_build_partial_solve_wit_4_pure : build_partial_solve_wit_4_pure.
Axiom proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4.
Axiom proof_of_build_partial_solve_wit_5_pure : build_partial_solve_wit_5_pure.
Axiom proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5.
Axiom proof_of_build_partial_solve_wit_6_pure : build_partial_solve_wit_6_pure.
Axiom proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6.
Axiom proof_of_build_partial_solve_wit_7 : build_partial_solve_wit_7.
Axiom proof_of_build_partial_solve_wit_8 : build_partial_solve_wit_8.
Axiom proof_of_build_partial_solve_wit_9_pure : build_partial_solve_wit_9_pure.
Axiom proof_of_build_partial_solve_wit_9 : build_partial_solve_wit_9.
Axiom proof_of_build_partial_solve_wit_10 : build_partial_solve_wit_10.
Axiom proof_of_build_partial_solve_wit_11 : build_partial_solve_wit_11.
Axiom proof_of_build_partial_solve_wit_12 : build_partial_solve_wit_12.
Axiom proof_of_build_partial_solve_wit_13 : build_partial_solve_wit_13.
Axiom proof_of_build_partial_solve_wit_14 : build_partial_solve_wit_14.

End VC_Correct.
