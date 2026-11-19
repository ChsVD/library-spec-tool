Historical generated build_safety_wit_4 from the QCP record-builtins diagnostic. Assess this particular antecedent and consequent. The snapshot is a historical context.

Definition build_safety_wit_4 := 
forall (head_pre: Z) (Rows_build_table: (@list build_row_snapshot)) (M_build_table: Z) (N_build_table: Z) (t_addr_row: Z) (t_addr_basic: Z) (t_addr_a: Z) (t_addr_c: Z) (t_addr_d: Z) (q: Z) (L: (@list Z)) (B: (@list Z)) (A: (@list Z)) (D: (@list Z)) (C: (@list Z)) (SuffixR: (@list build_row_snapshot)) (PrefixR: (@list build_row_snapshot)) (r: Z) (t_addr_cols: Z) (q_coef: Z) (q_next: Z) (Entry: build_row_snapshot) (Tail: (@list build_row_snapshot)) (PreH1 : (q <> 0)) (PreH2 : ((build_row_coefficients (Entry)) <> 0)) (PreH3 : (SuffixR = (build_cons (Entry) (Tail)))) (PreH4 : (q_next = (build_row_next (Entry)))) (PreH5 : (q_coef = (build_row_coefficients (Entry)))) (PreH6 : (r < M_build_table)) (PreH7 : (M_build_table = (Zlength (Rows_build_table)))) (PreH8 : (0 <= M_build_table)) (PreH9 : (M_build_table < UINT_MAX)) (PreH10 : (0 <= N_build_table)) (PreH11 : (N_build_table < UINT_MAX)) (PreH12 : ((M_build_table + N_build_table ) < UINT_MAX)) (PreH13 : ((N_build_table + 1 ) <= UINT_MAX)) (PreH14 : (0 <= (M_build_table * sizeof( "__mpz_struct" ) ))) (PreH15 : ((M_build_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH16 : (0 <= ((M_build_table * (M_build_table + N_build_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH17 : (((M_build_table * (M_build_table + N_build_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH18 : ((M_build_table * sizeof(UINT) ) <= INT_MAX)) (PreH19 : (((M_build_table + N_build_table ) * sizeof(UINT) ) <= INT_MAX)) (PreH20 : (((N_build_table + 1 ) * sizeof( "__mpz_struct" ) ) <= UINT_MAX)) (PreH21 : ((0 < M_build_table) -> (((N_build_table + 1 ) * sizeof( "__mpz_struct" ) ) <= INT_MAX))) (PreH22 : ((0 < M_build_table) -> (simplex_mpz_layout ))) (PreH23 : (t_addr_cols = (M_build_table + N_build_table ))) (PreH24 : (0 <= r)) (PreH25 : (r <= M_build_table)) (PreH26 : (r = (Zlength (PrefixR)))) (PreH27 : (Rows_build_table = (build_append (PrefixR) (SuffixR)))) (PreH28 : (simplex_built_dc Rows_build_table r D C )) (PreH29 : (simplex_built_a N_build_table M_build_table r 0 Rows_build_table A )) (PreH30 : (simplex_built_basis N_build_table r B )) (PreH31 : (simplex_built_lookup N_build_table M_build_table r L )) ,
  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> q_next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> q_coef)
  **  (simplex_mpz_live (build_row_coefficients (Entry)) 0 (N_build_table + 1 ) (build_row_entries (Entry)) )
  **  (build_input_segment (build_row_next (Entry)) 0 (N_build_table + 1 ) Tail )
  **  ((( &( "variables" ) )) # UInt  |-> N_build_table)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> M_build_table)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  (build_input_segment head_pre q (N_build_table + 1 ) PrefixR )
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> t_addr_d)
  **  (simplex_mpz_live t_addr_d 0 M_build_table D )
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> t_addr_c)
  **  (simplex_mpz_live t_addr_c 0 M_build_table C )
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> t_addr_a)
  **  (simplex_mpz_live t_addr_a 0 (M_build_table * (M_build_table + N_build_table ) ) A )
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> t_addr_basic)
  **  (UIntArray.seg t_addr_basic 0 r B )
  **  (UIntArray.undef_seg t_addr_basic r M_build_table )
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> t_addr_row)
  **  (UIntArray.full t_addr_row (M_build_table + N_build_table ) L )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

