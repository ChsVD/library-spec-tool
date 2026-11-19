From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.normalize_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function normalize -----*)

Definition normalize_safety_wit_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH6 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  ((( &( "slot" ) )) # UInt  |->_)
  **  (store_Z ( &( "g" ) ) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_2 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH16 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : (same_sign G gs )) (PreH18 : ((Zabs (gs)) <= gcap)) (PreH19 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_3 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH16 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : (same_sign G gs )) (PreH18 : ((Zabs (gs)) <= gcap)) (PreH19 : (gs = 1)) (PreH20 : (1 <= G)) (PreH21 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_4 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (j = (Znth slot N_normalize_staged_row 0))) (PreH19 : (0 <= j)) (PreH20 : (j < K_normalize_staged_row)) (PreH21 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH22 : (same_sign G gs )) (PreH23 : ((Zabs (gs)) <= gcap)) (PreH24 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_5 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (j = (Znth slot N_normalize_staged_row 0))) (PreH19 : (0 <= j)) (PreH20 : (j < K_normalize_staged_row)) (PreH21 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH22 : (same_sign G gs )) (PreH23 : ((Zabs (gs)) <= gcap)) (PreH24 : (gs = 1)) (PreH25 : (1 <= G)) (PreH26 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_6 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (same_sign G gs )) (PreH19 : ((Zabs (gs)) <= gcap)) (PreH20 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_7 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (gs <> 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (same_sign G gs )) (PreH19 : ((Zabs (gs)) <= gcap)) (PreH20 : (gs = 1)) (PreH21 : (1 <= G)) (PreH22 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_8 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (0 <= slot)) (PreH18 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (j = (Znth slot N_normalize_staged_row 0))) (PreH20 : (0 <= j)) (PreH21 : (j < K_normalize_staged_row)) (PreH22 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH23 : (same_sign G gs )) (PreH24 : ((Zabs (gs)) <= gcap)) (PreH25 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_9 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (gs <> 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (0 <= slot)) (PreH18 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (j = (Znth slot N_normalize_staged_row 0))) (PreH20 : (0 <= j)) (PreH21 : (j < K_normalize_staged_row)) (PreH22 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH23 : (same_sign G gs )) (PreH24 : ((Zabs (gs)) <= gcap)) (PreH25 : (gs = 1)) (PreH26 : (1 <= G)) (PreH27 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_10 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (same_sign G gs )) (PreH19 : ((Zabs (gs)) <= gcap)) (PreH20 : (gs = 1)) (PreH21 : (1 <= G)) (PreH22 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_11 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (0 <= slot)) (PreH18 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (j = (Znth slot N_normalize_staged_row 0))) (PreH20 : (0 <= j)) (PreH21 : (j < K_normalize_staged_row)) (PreH22 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH23 : (same_sign G gs )) (PreH24 : ((Zabs (gs)) <= gcap)) (PreH25 : (gs = 1)) (PreH26 : (1 <= G)) (PreH27 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_12 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (same_sign G gs )) (PreH19 : ((Zabs (gs)) <= gcap)) (PreH20 : (gs = 1)) (PreH21 : (1 <= G)) (PreH22 : (G <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_13 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (0 <= slot)) (PreH18 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (j = (Znth slot N_normalize_staged_row 0))) (PreH20 : (0 <= j)) (PreH21 : (j < K_normalize_staged_row)) (PreH22 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH23 : (same_sign G gs )) (PreH24 : ((Zabs (gs)) <= gcap)) (PreH25 : (gs = 1)) (PreH26 : (1 <= G)) (PreH27 : (G <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_14 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (K_normalize_staged_row < K_normalize_staged_row)) (PreH2 : (G <> 1)) (PreH3 : (gs = 1)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (same_sign G gs )) (PreH21 : ((Zabs (gs)) <= gcap)) (PreH22 : (gs = 1)) (PreH23 : (1 <= G)) (PreH24 : (G <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_15 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j >= K_normalize_staged_row)) (PreH2 : (G <> 1)) (PreH3 : (gs = 1)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (same_sign G gs )) (PreH26 : ((Zabs (gs)) <= gcap)) (PreH27 : (gs = 1)) (PreH28 : (1 <= G)) (PreH29 : (G <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_16 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (K_normalize_staged_row < K_normalize_staged_row)) (PreH2 : (gs <> 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (same_sign G gs )) (PreH20 : ((Zabs (gs)) <= gcap)) (PreH21 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_17 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j >= K_normalize_staged_row)) (PreH2 : (gs <> 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (j = (Znth slot N_normalize_staged_row 0))) (PreH21 : (0 <= j)) (PreH22 : (j < K_normalize_staged_row)) (PreH23 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH24 : (same_sign G gs )) (PreH25 : ((Zabs (gs)) <= gcap)) (PreH26 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_18 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : ((Znth j R_normalize_staged_row 0) <> UINT_MAX)) (PreH2 : (j < K_normalize_staged_row)) (PreH3 : (G <> 1)) (PreH4 : (gs = 1)) (PreH5 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH6 : (simplex_mpz_layout )) (PreH7 : (0 <= I_normalize_staged_row)) (PreH8 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH9 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH10 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH11 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH12 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : (K_normalize_staged_row < UINT_MAX)) (PreH14 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH18 : (0 < G)) (PreH19 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH20 : (0 <= slot)) (PreH21 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH22 : (j = (Znth slot N_normalize_staged_row 0))) (PreH23 : (0 <= j)) (PreH24 : (j < K_normalize_staged_row)) (PreH25 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH26 : (same_sign G gs )) (PreH27 : ((Zabs (gs)) <= gcap)) (PreH28 : (gs = 1)) (PreH29 : (1 <= G)) (PreH30 : (G <= UINT_MAX)),
  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_19 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : ((Znth j R_normalize_staged_row 0) <> UINT_MAX)) (PreH2 : (j < K_normalize_staged_row)) (PreH3 : (gs <> 1)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (same_sign G gs )) (PreH26 : ((Zabs (gs)) <= gcap)) (PreH27 : (gs <> 1)),
  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_20 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j = K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (gs <> 1)) (PreH5 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH6 : (simplex_mpz_layout )) (PreH7 : (0 <= I_normalize_staged_row)) (PreH8 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH9 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH10 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH11 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH12 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : (K_normalize_staged_row < UINT_MAX)) (PreH14 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH18 : (0 < G)) (PreH19 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH20 : (0 <= slot)) (PreH21 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH22 : (j = (Znth slot N_normalize_staged_row 0))) (PreH23 : (0 <= j)) (PreH24 : (j < K_normalize_staged_row)) (PreH25 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH26 : (same_sign G gs )) (PreH27 : ((Zabs (gs)) <= gcap)) (PreH28 : (gs <> 1)),
  ((( &( "x" ) )) # Ptr  |->_)
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_21 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j = K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (G <> 1)) (PreH5 : (gs = 1)) (PreH6 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH7 : (simplex_mpz_layout )) (PreH8 : (0 <= I_normalize_staged_row)) (PreH9 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH10 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH11 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH12 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH13 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : (K_normalize_staged_row < UINT_MAX)) (PreH15 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH17 : (0 <= slot)) (PreH18 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (0 < G)) (PreH20 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH27 : (same_sign G gs )) (PreH28 : ((Zabs (gs)) <= gcap)) (PreH29 : (gs = 1)) (PreH30 : (1 <= G)) (PreH31 : (G <= UINT_MAX)),
  ((( &( "x" ) )) # Ptr  |->_)
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_22 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign X size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (j = (Znth slot N_normalize_staged_row 0))) (PreH21 : (0 <= j)) (PreH22 : (j < K_normalize_staged_row)) (PreH23 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH24 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH25 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_23 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign X size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH20 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_24 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (size <> 0)) (PreH4 : (same_sign X size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH7 : (simplex_mpz_layout )) (PreH8 : (0 <= I_normalize_staged_row)) (PreH9 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH10 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH11 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH12 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH13 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : (K_normalize_staged_row < UINT_MAX)) (PreH15 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH17 : (0 <= slot)) (PreH18 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (0 < G)) (PreH20 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH27 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH28 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_25 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (size <> 0)) (PreH4 : (same_sign X size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH7 : (simplex_mpz_layout )) (PreH8 : (0 <= I_normalize_staged_row)) (PreH9 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH10 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH11 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH12 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH13 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : (K_normalize_staged_row < UINT_MAX)) (PreH15 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH17 : (0 <= slot)) (PreH18 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (0 < G)) (PreH20 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH21 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH22 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH23 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_26 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G)) (PreH13 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (same_sign G gs )) (PreH15 : ((Zabs (gs)) <= gcap)) (PreH16 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_27 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G)) (PreH13 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (same_sign G gs )) (PreH15 : ((Zabs (gs)) <= gcap)) (PreH16 : (gs = 1)) (PreH17 : (1 <= G)) (PreH18 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_28 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G)) (PreH14 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs <> 1)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_29 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs <> 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G)) (PreH14 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs = 1)) (PreH18 : (1 <= G)) (PreH19 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ False ”
.

Definition normalize_safety_wit_30 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G)) (PreH14 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs = 1)) (PreH18 : (1 <= G)) (PreH19 : (G <= UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_31 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G)) (PreH14 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs = 1)) (PreH18 : (1 <= G)) (PreH19 : (G <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition normalize_safety_wit_32 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (Rem: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G)) (PreH13 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (( &( "tmp" ) ) <> 0)) (PreH15 : (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G )),
  ((( &( "slot" ) )) # UInt  |->_)
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_33 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z) (slot: Z) (PreH1 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_34 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z) (slot: Z) (PreH1 : (slot > (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (Ca = C_normalize_staged_row)) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_35 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j >= K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_36 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j < K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_37 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_38 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (PreH1 : (K_normalize_staged_row < K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_39 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j >= K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (Ca = C_normalize_staged_row)) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_40 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (PreH1 : (K_normalize_staged_row < K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (Ca = C_normalize_staged_row)) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_41 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (PreH1 : ((Znth j R_normalize_staged_row 0) <> UINT_MAX)) (PreH2 : (j < K_normalize_staged_row)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_42 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j = K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (0 <= slot)) (PreH24 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (j = (Znth slot N_normalize_staged_row 0))) (PreH26 : (0 <= j)) (PreH27 : (j < K_normalize_staged_row)) (PreH28 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  ((( &( "x" ) )) # Ptr  |->_)
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_43 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign X size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH19 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH22 : (( &( "tmp" ) ) <> 0)) (PreH23 : (pivot_divides_exactly X G )) (PreH24 : (0 <= slot)) (PreH25 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (j = (Znth slot N_normalize_staged_row 0))) (PreH27 : (0 <= j)) (PreH28 : (j < K_normalize_staged_row)) (PreH29 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH30 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH31 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_44 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign X size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH19 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH22 : (( &( "tmp" ) ) <> 0)) (PreH23 : (pivot_divides_exactly X G )) (PreH24 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH26 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_45 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign X size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH22 : (( &( "tmp" ) ) <> 0)) (PreH23 : (pivot_divides_exactly X G )) (PreH24 : (0 <= slot)) (PreH25 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (j = (Znth slot N_normalize_staged_row 0))) (PreH27 : (0 <= j)) (PreH28 : (j < K_normalize_staged_row)) (PreH29 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH30 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH31 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_46 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign X size )) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH22 : (( &( "tmp" ) ) <> 0)) (PreH23 : (pivot_divides_exactly X G )) (PreH24 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH26 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition normalize_safety_wit_47 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_48 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_49 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_safety_wit_50 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ False ”
.

Definition normalize_entail_wit_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (r_pre: Z) (PreH1 : (r_pre = I_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH7 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (store_Z ( &( "remainder" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "g" ) ) 0 )
  **  ((( &( "r" ) )) # UInt  |-> r_pre)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (r_pre: Z) (PreH1 : (r_pre = I_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH7 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (store_Z ( &( "remainder" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "g" ) ) 0 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
|--
  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
).

Definition normalize_entail_wit_1_split_goal_spatial :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (r_pre: Z) (PreH1 : (r_pre = I_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH7 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (store_Z ( &( "remainder" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "g" ) ) 0 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
|--
  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
.

Definition normalize_entail_wit_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH6 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (store_Z ( &( "g" ) ) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (0) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH6 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (store_Z ( &( "g" ) ) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
|--
  EX (Rem: Z) (T: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (0) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (0) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_3_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem_2: Z) (T_2: Z) (G_2: Z) (slot: Z) (PreH1 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
  ||
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs <> 1) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
.

Definition normalize_entail_wit_3_2 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem_2: Z) (T_2: Z) (G_2: Z) (slot: Z) (PreH1 : (slot <> (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))),
  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  ((( &( "j" ) )) # UInt  |-> (Znth slot N_normalize_staged_row 0))
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (j: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
  ||
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (j_2: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j_2 = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j_2) ”
  &&  “ (j_2 < K_normalize_staged_row) ”
  &&  “ ((Znth j_2 R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs <> 1) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
.

Definition normalize_entail_wit_4_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (gs <> 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (same_sign G_2 gs )) (PreH20 : ((Zabs (gs)) <= gcap)) (PreH21 : (gs <> 1)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G_2)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (X: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (gs <> 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (same_sign G_2 gs )) (PreH20 : ((Zabs (gs)) <= gcap)) (PreH21 : (gs <> 1)),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G_2)) (Zabs (gs)) )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (Zabs (gs)) )
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_4_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (G_2 <> 1)) (PreH3 : (gs = 1)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (same_sign G_2 gs )) (PreH21 : ((Zabs (gs)) <= gcap)) (PreH22 : (gs = 1)) (PreH23 : (1 <= G_2)) (PreH24 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (X: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (G_2 <> 1)) (PreH3 : (gs = 1)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (same_sign G_2 gs )) (PreH21 : ((Zabs (gs)) <= gcap)) (PreH22 : (gs = 1)) (PreH23 : (1 <= G_2)) (PreH24 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (Zabs (gs)) )
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_4_3 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j <> K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (gs <> 1)) (PreH5 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH6 : (simplex_mpz_layout )) (PreH7 : (0 <= I_normalize_staged_row)) (PreH8 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH9 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH10 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH11 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH12 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : (K_normalize_staged_row < UINT_MAX)) (PreH14 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH18 : (0 < G_2)) (PreH19 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH20 : (0 <= slot)) (PreH21 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH22 : (j = (Znth slot N_normalize_staged_row 0))) (PreH23 : (0 <= j)) (PreH24 : (j < K_normalize_staged_row)) (PreH25 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH26 : (same_sign G_2 gs )) (PreH27 : ((Zabs (gs)) <= gcap)) (PreH28 : (gs <> 1)),
  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G_2)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (X: Z) (j_2: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j_2 = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j_2) ”
  &&  “ (j_2 < K_normalize_staged_row) ”
  &&  “ ((Znth j_2 R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ ((AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j_2 ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j_2 ) A_normalize_staged_row 0)) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j_2)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j_2 ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j <> K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (gs <> 1)) (PreH5 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH6 : (simplex_mpz_layout )) (PreH7 : (0 <= I_normalize_staged_row)) (PreH8 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH9 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH10 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH11 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH12 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : (K_normalize_staged_row < UINT_MAX)) (PreH14 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH18 : (0 < G_2)) (PreH19 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH20 : (0 <= slot)) (PreH21 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH22 : (j = (Znth slot N_normalize_staged_row 0))) (PreH23 : (0 <= j)) (PreH24 : (j < K_normalize_staged_row)) (PreH25 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH26 : (same_sign G_2 gs )) (PreH27 : ((Zabs (gs)) <= gcap)) (PreH28 : (gs <> 1)),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G_2)) (Zabs (gs)) )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (0 <= (Znth slot N_normalize_staged_row 0)) ”
  &&  “ ((Znth slot N_normalize_staged_row 0) < K_normalize_staged_row) ”
  &&  “ ((Znth (Znth slot N_normalize_staged_row 0) R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ ((AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) * sizeof( "__mpz_struct" )))) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (Zabs (gs)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_4_4 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j <> K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (G_2 <> 1)) (PreH5 : (gs = 1)) (PreH6 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH7 : (simplex_mpz_layout )) (PreH8 : (0 <= I_normalize_staged_row)) (PreH9 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH10 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH11 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH12 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH13 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : (K_normalize_staged_row < UINT_MAX)) (PreH15 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH17 : (0 <= slot)) (PreH18 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (0 < G_2)) (PreH20 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH27 : (same_sign G_2 gs )) (PreH28 : ((Zabs (gs)) <= gcap)) (PreH29 : (gs = 1)) (PreH30 : (1 <= G_2)) (PreH31 : (G_2 <= UINT_MAX)),
  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (X: Z) (j_2: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j_2 = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j_2) ”
  &&  “ (j_2 < K_normalize_staged_row) ”
  &&  “ ((Znth j_2 R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ ((AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j_2 ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j_2 ) A_normalize_staged_row 0)) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j_2)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j_2 ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j <> K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (G_2 <> 1)) (PreH5 : (gs = 1)) (PreH6 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH7 : (simplex_mpz_layout )) (PreH8 : (0 <= I_normalize_staged_row)) (PreH9 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH10 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH11 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH12 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH13 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : (K_normalize_staged_row < UINT_MAX)) (PreH15 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH17 : (0 <= slot)) (PreH18 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (0 < G_2)) (PreH20 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH27 : (same_sign G_2 gs )) (PreH28 : ((Zabs (gs)) <= gcap)) (PreH29 : (gs = 1)) (PreH30 : (1 <= G_2)) (PreH31 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (0 <= (Znth slot N_normalize_staged_row 0)) ”
  &&  “ ((Znth slot N_normalize_staged_row 0) < K_normalize_staged_row) ”
  &&  “ ((Znth (Znth slot N_normalize_staged_row 0) R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ ((AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) * sizeof( "__mpz_struct" )))) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (Zabs (gs)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z (AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_5_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  (store_Z ( &( "g" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  (store_Z ( &( "g" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
|--
  EX (Rem: Z) (T: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_5_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  (store_Z ( &( "g" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  (store_Z ( &( "g" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
|--
  EX (Rem: Z) (T: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_5_3 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH26 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (size = 0)) (PreH6 : (same_sign X size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH9 : (simplex_mpz_layout )) (PreH10 : (0 <= I_normalize_staged_row)) (PreH11 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH12 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH13 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH14 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH15 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : (K_normalize_staged_row < UINT_MAX)) (PreH17 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (0 < G_2)) (PreH22 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH23 : (0 <= slot)) (PreH24 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (j = (Znth slot N_normalize_staged_row 0))) (PreH26 : (0 <= j)) (PreH27 : (j < K_normalize_staged_row)) (PreH28 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH29 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH30 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_5_4 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH21 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (size = 0)) (PreH6 : (same_sign X size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH9 : (simplex_mpz_layout )) (PreH10 : (0 <= I_normalize_staged_row)) (PreH11 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH12 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH13 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH14 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH15 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : (K_normalize_staged_row < UINT_MAX)) (PreH17 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (0 < G_2)) (PreH22 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH23 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH25 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_5_5 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign Rem size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (Rem)) (Zabs (size_2)) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
).

Definition normalize_entail_wit_5_6 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G_2)) (PreH21 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign Rem size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (Rem)) (Zabs (size_2)) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((slot + 1 )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) T )
).

Definition normalize_entail_wit_6_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem_2: Z) (T_2: Z) (G_2: Z) (slot: Z) (PreH1 : (slot > (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G_2)) (PreH16 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
  ||
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs <> 1) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
.

Definition normalize_entail_wit_6_2 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs_2: Z) (gcap_2: Z) (gd_2: Z) (slot: Z) (j: Z) (PreH1 : (G_2 = 1)) (PreH2 : (gs_2 = 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (j = (Znth slot N_normalize_staged_row 0))) (PreH21 : (0 <= j)) (PreH22 : (j < K_normalize_staged_row)) (PreH23 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH24 : (same_sign G_2 gs_2 )) (PreH25 : ((Zabs (gs_2)) <= gcap_2)) (PreH26 : (gs_2 = 1)) (PreH27 : (1 <= G_2)) (PreH28 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd_2 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd_2)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (UIntArray.undef_seg gd_2 (Zabs (gs_2)) gcap_2 )
|--
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
  ||
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs <> 1) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
.

Definition normalize_entail_wit_6_3 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs_2: Z) (gcap_2: Z) (gd_2: Z) (slot: Z) (PreH1 : (G_2 = 1)) (PreH2 : (gs_2 = 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (same_sign G_2 gs_2 )) (PreH20 : ((Zabs (gs_2)) <= gcap_2)) (PreH21 : (gs_2 = 1)) (PreH22 : (1 <= G_2)) (PreH23 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd_2 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd_2)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (UIntArray.undef_seg gd_2 (Zabs (gs_2)) gcap_2 )
|--
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
  ||
  (EX (Rem: Z) (T: Z) (gd: Z) (gcap: Z) (gs: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs <> 1) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap ))
.

Definition normalize_entail_wit_7_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs <> 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G_2)) (PreH14 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G_2 gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs <> 1)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G_2)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs <> 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G_2)) (PreH14 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G_2 gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs <> 1)),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G_2)) (Zabs (gs)) )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (Zabs (gs)) )
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_7_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (G_2 <> 1)) (PreH2 : (gs = 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 < G_2)) (PreH15 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (same_sign G_2 gs )) (PreH17 : ((Zabs (gs)) <= gcap)) (PreH18 : (gs = 1)) (PreH19 : (1 <= G_2)) (PreH20 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (G_2 <> 1)) (PreH2 : (gs = 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 < G_2)) (PreH15 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (same_sign G_2 gs )) (PreH17 : ((Zabs (gs)) <= gcap)) (PreH18 : (gs = 1)) (PreH19 : (1 <= G_2)) (PreH20 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z),
  “ (same_sign (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (Zabs (gs)) )
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_8 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (Rem_2: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G_2)) (PreH13 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (( &( "tmp" ) ) <> 0)) (PreH15 : (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G_2 )),
  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (0) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (Rem_2: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G_2)) (PreH13 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (( &( "tmp" ) ) <> 0)) (PreH15 : (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G_2 )),
  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min (0) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_9_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem_2: Z) (T_2: Z) (Aa_2: (@list Z)) (Ca_2: (@list Z)) (Da_2: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca_2 = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (Rem_2: Z) (T_2: Z) (Aa_2: (@list Z)) (Ca_2: (@list Z)) (Da_2: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca_2 = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_9_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem_2: Z) (T_2: Z) (Aa_2: (@list Z)) (Ca_2: (@list Z)) (Da_2: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot <> (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca_2 = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )),
  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  ((( &( "j" ) )) # UInt  |-> (Znth slot N_normalize_staged_row 0))
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (j: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (Rem_2: Z) (T_2: Z) (Aa_2: (@list Z)) (Ca_2: (@list Z)) (Da_2: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot <> (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G_2)) (PreH17 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca_2 = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (0 <= (Znth slot N_normalize_staged_row 0)) ”
  &&  “ ((Znth slot N_normalize_staged_row 0) < K_normalize_staged_row) ”
  &&  “ ((Znth (Znth slot N_normalize_staged_row 0) R_normalize_staged_row 0) = UINT_MAX) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_10_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G_2)) (PreH16 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH18 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (Ca_2 = C_normalize_staged_row)) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH21 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (X: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row Ca 0)) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (PreH1 : (K_normalize_staged_row >= K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G_2)) (PreH16 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH18 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (Ca_2 = C_normalize_staged_row)) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH21 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row C_normalize_staged_row 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_10_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j <> K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (0 <= slot)) (PreH24 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (j = (Znth slot N_normalize_staged_row 0))) (PreH26 : (0 <= j)) (PreH27 : (j < K_normalize_staged_row)) (PreH28 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (j_3: Z) (X: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j_3 = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j_3) ”
  &&  “ (j_3 < K_normalize_staged_row) ”
  &&  “ ((Znth j_3 R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ ((AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j_3 ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j_3 ) Aa 0)) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "j" ) )) # UInt  |-> j_3)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j_3 ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z (AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j <> K_normalize_staged_row)) (PreH2 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH3 : (j < K_normalize_staged_row)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (0 <= slot)) (PreH24 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (j = (Znth slot N_normalize_staged_row 0))) (PreH26 : (0 <= j)) (PreH27 : (j < K_normalize_staged_row)) (PreH28 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (0 <= (Znth slot N_normalize_staged_row 0)) ”
  &&  “ ((Znth slot N_normalize_staged_row 0) < K_normalize_staged_row) ”
  &&  “ ((Znth (Znth slot N_normalize_staged_row 0) R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ ((AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) * sizeof( "__mpz_struct" )))) ”
  &&  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z (AP_normalize_staged_row + (((unsigned_last_nbits ((I_normalize_staged_row * K_normalize_staged_row )) (32)) + j ) * sizeof( "__mpz_struct" ))) (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa 0) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_11_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G_2 )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa_2 0))),
  (store_Z x ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa_2 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa_2 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G_2 )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa_2 0))),
  (store_Z x ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa_2 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa_2 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_11_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G_2 )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca_2 0))),
  (store_Z x ((Znth I_normalize_staged_row C_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row C_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row))) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G_2 )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca_2 0))),
  (store_Z x ((Znth I_normalize_staged_row C_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row C_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (C_normalize_staged_row)) )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_11_3 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G_2 )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa_2 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (size = 0)) (PreH6 : (same_sign X size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH9 : (simplex_mpz_layout )) (PreH10 : (0 <= I_normalize_staged_row)) (PreH11 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH12 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH13 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH14 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH15 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : (K_normalize_staged_row < UINT_MAX)) (PreH17 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (0 < G_2)) (PreH22 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH23 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH24 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (Ca_2 = C_normalize_staged_row)) (PreH26 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH27 : (( &( "tmp" ) ) <> 0)) (PreH28 : (pivot_divides_exactly X G_2 )) (PreH29 : (0 <= slot)) (PreH30 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH31 : (j = (Znth slot N_normalize_staged_row 0))) (PreH32 : (0 <= j)) (PreH33 : (j < K_normalize_staged_row)) (PreH34 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH35 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH36 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa_2 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca_2 )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_11_4 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G_2)) (PreH18 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca_2 = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G_2 )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca_2 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row))) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (X: Z) (Da_2: (@list Z)) (Ca_2: (@list Z)) (Aa_2: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (size = 0)) (PreH6 : (same_sign X size )) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH9 : (simplex_mpz_layout )) (PreH10 : (0 <= I_normalize_staged_row)) (PreH11 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH12 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH13 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH14 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH15 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH16 : (K_normalize_staged_row < UINT_MAX)) (PreH17 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH21 : (0 < G_2)) (PreH22 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH23 : (Da_2 = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH24 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH25 : (Ca_2 = C_normalize_staged_row)) (PreH26 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa_2 )) (PreH27 : (( &( "tmp" ) ) <> 0)) (PreH28 : (pivot_divides_exactly X G_2 )) (PreH29 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH30 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH31 : (X = (Znth I_normalize_staged_row Ca_2 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa_2 )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da_2 )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (Aa: (@list Z)),
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= (slot + 1 )) ”
  &&  “ ((slot + 1 ) <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ ((slot + 1 ) = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) (Z.min ((slot + 1 )) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (D_normalize_staged_row)) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))))) (C_normalize_staged_row)) )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_entail_wit_12_1 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem_2: Z) (T_2: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot > (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G_2)) (PreH16 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G_2))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G_2 )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (G: Z) (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)),
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot > (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G_2)) (PreH16 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G_2))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )),
  TT && emp 
|--
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Da Ca Aa ) ”
  &&  emp
).

Definition normalize_entail_wit_12_1_split_goal_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G_2: Z) (slot: Z) (PreH1 : (slot > (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G_2)) (PreH16 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G_2))) (D_normalize_staged_row)))) (PreH18 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH19 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G_2))) (C_normalize_staged_row)))) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G_2 (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )),
  (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Da Ca Aa )
.

Definition normalize_entail_wit_12_2 :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (G_2 = 1)) (PreH2 : (gs = 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 < G_2)) (PreH15 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (same_sign G_2 gs )) (PreH17 : ((Zabs (gs)) <= gcap)) (PreH18 : (gs = 1)) (PreH19 : (1 <= G_2)) (PreH20 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  EX (Rem: Z) (T: Z) (G: Z) (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)),
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (G_2: Z) (T_2: Z) (Rem_2: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (G_2 = 1)) (PreH2 : (gs = 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 < G_2)) (PreH15 : (G_2 = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (same_sign G_2 gs )) (PreH17 : ((Zabs (gs)) <= gcap)) (PreH18 : (gs = 1)) (PreH19 : (1 <= G_2)) (PreH20 : (G_2 <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G_2) ((cons (G_2) ((@nil Z))))) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T_2 )
  **  (store_Z ( &( "remainder" ) ) Rem_2 )
|--
  EX (Rem: Z) (T: Z) (G: Z) (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)),
  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
).

Definition normalize_return_wit_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Dn_2: (@list Z)) (Cn_2: (@list Z)) (An_2: (@list Z)) (PreH1 : (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn_2 Cn_2 An_2 )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn_2 )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn_2 )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An_2 )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  EX (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)),
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (r_pre: Z) (PreH1 : (r_pre = I_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH7 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (UndefStructPred__mpz_struct ( &( "tmp" ) ) )
  **  (UndefStructPred__mpz_struct ( &( "g" ) ) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  “ (r_pre = I_normalize_staged_row) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |->_)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |->_)
  **  (UndefStructPred__mpz_struct ( &( "tmp" ) ) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_2 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (r_pre: Z) (PreH1 : (r_pre = I_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH7 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (store_Z ( &( "g" ) ) 0 )
  **  (UndefStructPred__mpz_struct ( &( "tmp" ) ) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  “ (r_pre = I_normalize_staged_row) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  ((&(( &( "tmp" ) )->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&(( &( "tmp" ) )->ₛ "_mp_size")) # Int  |->_)
  **  ((&(( &( "tmp" ) )->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z ( &( "g" ) ) 0 )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_3 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (r_pre: Z) (PreH1 : (r_pre = I_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH7 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  (UndefStructPred__mpz_struct ( &( "remainder" ) ) )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "g" ) ) 0 )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  “ (r_pre = I_normalize_staged_row) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |->_)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "g" ) ) 0 )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_4 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH6 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) 0 )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
|--
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  (store_Z ( &( "g" ) ) 0 )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) 0 )
  **  (store_Z ( &( "remainder" ) ) 0 )
.

Definition normalize_partial_solve_wit_5 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem: Z) (T: Z) (G: Z) (slot: Z) (PreH1 : (slot <> (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (slot <> (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  (((NP_normalize_staged_row + (slot * sizeof(UINT)))) # UInt  |-> (Znth slot N_normalize_staged_row 0))
  **  (UIntArray.missing_i NP_normalize_staged_row slot 0 (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_6 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (same_sign G gs )) (PreH19 : ((Zabs (gs)) <= gcap)) (PreH20 : (gs = 1)) (PreH21 : (1 <= G)) (PreH22 : (G <= UINT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (gs = 1) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  (((gd + (0 * sizeof(UINT)))) # UInt  |-> G)
  **  (UIntArray.missing_i gd 0 0 1 (cons (G) ((@nil Z))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
.

Definition normalize_partial_solve_wit_7 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH17 : (0 <= slot)) (PreH18 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (j = (Znth slot N_normalize_staged_row 0))) (PreH20 : (0 <= j)) (PreH21 : (j < K_normalize_staged_row)) (PreH22 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH23 : (same_sign G gs )) (PreH24 : ((Zabs (gs)) <= gcap)) (PreH25 : (gs = 1)) (PreH26 : (1 <= G)) (PreH27 : (G <= UINT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (gs = 1) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  (((gd + (0 * sizeof(UINT)))) # UInt  |-> G)
  **  (UIntArray.missing_i gd 0 0 1 (cons (G) ((@nil Z))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
.

Definition normalize_partial_solve_wit_8 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j < K_normalize_staged_row)) (PreH2 : (G <> 1)) (PreH3 : (gs = 1)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (same_sign G gs )) (PreH26 : ((Zabs (gs)) <= gcap)) (PreH27 : (gs = 1)) (PreH28 : (1 <= G)) (PreH29 : (G <= UINT_MAX)),
  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (j < K_normalize_staged_row) ”
  &&  “ (G <> 1) ”
  &&  “ (gs = 1) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  (((RP_normalize_staged_row + (j * sizeof(UINT)))) # UInt  |-> (Znth j R_normalize_staged_row 0))
  **  (UIntArray.missing_i RP_normalize_staged_row j 0 K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full gd 1 (replace_Znth (0) (G) ((cons (G) ((@nil Z))))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
.

Definition normalize_partial_solve_wit_9 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (slot: Z) (j: Z) (PreH1 : (j < K_normalize_staged_row)) (PreH2 : (gs <> 1)) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (j = (Znth slot N_normalize_staged_row 0))) (PreH21 : (0 <= j)) (PreH22 : (j < K_normalize_staged_row)) (PreH23 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH24 : (same_sign G gs )) (PreH25 : ((Zabs (gs)) <= gcap)) (PreH26 : (gs <> 1)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (j < K_normalize_staged_row) ”
  &&  “ (gs <> 1) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs <> 1) ”
  &&  (((RP_normalize_staged_row + (j * sizeof(UINT)))) # UInt  |-> (Znth j R_normalize_staged_row 0))
  **  (UIntArray.missing_i RP_normalize_staged_row j 0 K_normalize_staged_row R_normalize_staged_row )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (mpd_store_Z_compact UINT_MOD gd (Zabs (G)) (Zabs (gs)) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
.

Definition normalize_partial_solve_wit_10 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (j = (Znth slot N_normalize_staged_row 0))) (PreH19 : (0 <= j)) (PreH20 : (j < K_normalize_staged_row)) (PreH21 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH22 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH23 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z x X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ”
  &&  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_11 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH16 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH18 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (store_Z x X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_12_pure :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH26 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) <> 0) ”
  &&  “ (( &( "remainder" ) ) <> 0) ”
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (j <= UINT_MAX)) (PreH2 : (slot <= UINT_MAX)) (PreH3 : (K_normalize_staged_row <= UINT_MAX)) (PreH4 : (M_normalize_staged_row <= UINT_MAX)) (PreH5 : (I_normalize_staged_row <= UINT_MAX)) (PreH6 : (j >= 0)) (PreH7 : (slot >= 0)) (PreH8 : (K_normalize_staged_row >= 0)) (PreH9 : (M_normalize_staged_row >= 0)) (PreH10 : (I_normalize_staged_row >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (size <= INT_MAX)) (PreH13 : (cap >= INT_MIN)) (PreH14 : (size >= INT_MIN)) (PreH15 : (size <> 0)) (PreH16 : (same_sign X size )) (PreH17 : ((Zabs (size)) <= cap)) (PreH18 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH19 : (simplex_mpz_layout )) (PreH20 : (0 <= I_normalize_staged_row)) (PreH21 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH22 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH23 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH24 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH25 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (K_normalize_staged_row < UINT_MAX)) (PreH27 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH28 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH29 : (0 <= slot)) (PreH30 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH31 : (0 < G)) (PreH32 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH33 : (0 <= slot)) (PreH34 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH35 : (j = (Znth slot N_normalize_staged_row 0))) (PreH36 : (0 <= j)) (PreH37 : (j < K_normalize_staged_row)) (PreH38 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH39 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH40 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "remainder" ) ) <> 0) ”
).

Definition normalize_partial_solve_wit_12_pure_split_goal_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (j <= UINT_MAX)) (PreH2 : (slot <= UINT_MAX)) (PreH3 : (K_normalize_staged_row <= UINT_MAX)) (PreH4 : (M_normalize_staged_row <= UINT_MAX)) (PreH5 : (I_normalize_staged_row <= UINT_MAX)) (PreH6 : (j >= 0)) (PreH7 : (slot >= 0)) (PreH8 : (K_normalize_staged_row >= 0)) (PreH9 : (M_normalize_staged_row >= 0)) (PreH10 : (I_normalize_staged_row >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (size <= INT_MAX)) (PreH13 : (cap >= INT_MIN)) (PreH14 : (size >= INT_MIN)) (PreH15 : (size <> 0)) (PreH16 : (same_sign X size )) (PreH17 : ((Zabs (size)) <= cap)) (PreH18 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH19 : (simplex_mpz_layout )) (PreH20 : (0 <= I_normalize_staged_row)) (PreH21 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH22 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH23 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH24 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH25 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (K_normalize_staged_row < UINT_MAX)) (PreH27 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH28 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH29 : (0 <= slot)) (PreH30 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH31 : (0 < G)) (PreH32 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH33 : (0 <= slot)) (PreH34 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH35 : (j = (Znth slot N_normalize_staged_row 0))) (PreH36 : (0 <= j)) (PreH37 : (j < K_normalize_staged_row)) (PreH38 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH39 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH40 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "remainder" ) ) <> 0) ”
.

Definition normalize_partial_solve_wit_12_aux :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH26 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) <> 0) ”
  &&  “ (( &( "remainder" ) ) <> 0) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ”
  &&  (store_Z ( &( "remainder" ) ) Rem )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
.

Definition normalize_partial_solve_wit_12 := normalize_partial_solve_wit_12_pure -> normalize_partial_solve_wit_12_aux.

Definition normalize_partial_solve_wit_13_pure :=
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH21 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) <> 0) ”
  &&  “ (( &( "remainder" ) ) <> 0) ”
) \/
(
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (slot <= UINT_MAX)) (PreH2 : (K_normalize_staged_row <= UINT_MAX)) (PreH3 : (M_normalize_staged_row <= UINT_MAX)) (PreH4 : (I_normalize_staged_row <= UINT_MAX)) (PreH5 : (slot >= 0)) (PreH6 : (K_normalize_staged_row >= 0)) (PreH7 : (M_normalize_staged_row >= 0)) (PreH8 : (I_normalize_staged_row >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (size <= INT_MAX)) (PreH11 : (cap >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (size <> 0)) (PreH14 : (same_sign X size )) (PreH15 : ((Zabs (size)) <= cap)) (PreH16 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH17 : (simplex_mpz_layout )) (PreH18 : (0 <= I_normalize_staged_row)) (PreH19 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH20 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH21 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH22 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH23 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (K_normalize_staged_row < UINT_MAX)) (PreH25 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH27 : (0 <= slot)) (PreH28 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH29 : (0 < G)) (PreH30 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH31 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH32 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH33 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "remainder" ) ) <> 0) ”
  &&  “ ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) <> 0) ”
).

Definition normalize_partial_solve_wit_13_pure_split_goal_1 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (slot <= UINT_MAX)) (PreH2 : (K_normalize_staged_row <= UINT_MAX)) (PreH3 : (M_normalize_staged_row <= UINT_MAX)) (PreH4 : (I_normalize_staged_row <= UINT_MAX)) (PreH5 : (slot >= 0)) (PreH6 : (K_normalize_staged_row >= 0)) (PreH7 : (M_normalize_staged_row >= 0)) (PreH8 : (I_normalize_staged_row >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (size <= INT_MAX)) (PreH11 : (cap >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (size <> 0)) (PreH14 : (same_sign X size )) (PreH15 : ((Zabs (size)) <= cap)) (PreH16 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH17 : (simplex_mpz_layout )) (PreH18 : (0 <= I_normalize_staged_row)) (PreH19 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH20 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH21 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH22 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH23 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (K_normalize_staged_row < UINT_MAX)) (PreH25 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH27 : (0 <= slot)) (PreH28 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH29 : (0 < G)) (PreH30 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH31 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH32 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH33 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "remainder" ) ) <> 0) ”
.

Definition normalize_partial_solve_wit_13_pure_split_goal_2 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (slot <= UINT_MAX)) (PreH2 : (K_normalize_staged_row <= UINT_MAX)) (PreH3 : (M_normalize_staged_row <= UINT_MAX)) (PreH4 : (I_normalize_staged_row <= UINT_MAX)) (PreH5 : (slot >= 0)) (PreH6 : (K_normalize_staged_row >= 0)) (PreH7 : (M_normalize_staged_row >= 0)) (PreH8 : (I_normalize_staged_row >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (size <= INT_MAX)) (PreH11 : (cap >= INT_MIN)) (PreH12 : (size >= INT_MIN)) (PreH13 : (size <> 0)) (PreH14 : (same_sign X size )) (PreH15 : ((Zabs (size)) <= cap)) (PreH16 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH17 : (simplex_mpz_layout )) (PreH18 : (0 <= I_normalize_staged_row)) (PreH19 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH20 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH21 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH22 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH23 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (K_normalize_staged_row < UINT_MAX)) (PreH25 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH27 : (0 <= slot)) (PreH28 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH29 : (0 < G)) (PreH30 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH31 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH32 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH33 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) <> 0) ”
.

Definition normalize_partial_solve_wit_13_aux :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH21 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) <> 0) ”
  &&  “ (( &( "remainder" ) ) <> 0) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  (store_Z ( &( "remainder" ) ) Rem )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
.

Definition normalize_partial_solve_wit_13 := normalize_partial_solve_wit_13_pure -> normalize_partial_solve_wit_13_aux.

Definition normalize_partial_solve_wit_14 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (0 <= slot)) (PreH20 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (j = (Znth slot N_normalize_staged_row 0))) (PreH22 : (0 <= j)) (PreH23 : (j < K_normalize_staged_row)) (PreH24 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH25 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH26 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  EX (ptr: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ”
  &&  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
.

Definition normalize_partial_solve_wit_15 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH19 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH21 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  EX (ptr: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
.

Definition normalize_partial_solve_wit_16 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G)) (PreH21 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  “ (size_2 <> 0) ”
  &&  “ (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ”
  &&  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_17 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (ptr: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G)) (PreH21 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) (Zabs (size_2)) )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  “ (size_2 <> 0) ”
  &&  “ (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_18 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (X: Z) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G)) (PreH21 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0))),
  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  “ (size_2 <> 0) ”
  &&  “ (same_sign (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0)) ”
  &&  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) A_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) A_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_19 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (X: Z) (slot: Z) (x: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size <> 0)) (PreH5 : (same_sign X size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH8 : (simplex_mpz_layout )) (PreH9 : (0 <= I_normalize_staged_row)) (PreH10 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH11 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH12 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH13 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH14 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH15 : (K_normalize_staged_row < UINT_MAX)) (PreH16 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH17 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH20 : (0 < G)) (PreH21 : (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row C_normalize_staged_row 0))),
  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
|--
  “ (size_2 <> 0) ”
  &&  “ (same_sign (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (slot) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row C_normalize_staged_row 0)) ”
  &&  (store_Z ( &( "g" ) ) (normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))) )
  **  (store_Z ( &( "tmp" ) ) (Zgcd ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row))))) ((Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))))) )
  **  (store_Z ( &( "remainder" ) ) (Z.rem ((Znth I_normalize_staged_row C_normalize_staged_row 0)) ((normalize_prefix_gcd ((Znth I_normalize_staged_row D_normalize_staged_row 0)) ((K_normalize_staged_row - M_normalize_staged_row )) ((normalize_row_values (K_normalize_staged_row) (I_normalize_staged_row) (A_normalize_staged_row) (C_normalize_staged_row) (N_normalize_staged_row)))))) )
  **  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Definition normalize_partial_solve_wit_20 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (gs: Z) (gcap: Z) (gd: Z) (PreH1 : (gs = 1)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 < G)) (PreH14 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH15 : (same_sign G gs )) (PreH16 : ((Zabs (gs)) <= gcap)) (PreH17 : (gs = 1)) (PreH18 : (1 <= G)) (PreH19 : (G <= UINT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.full gd 1 (cons (G) ((@nil Z))) )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
|--
  “ (gs = 1) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (same_sign G gs ) ”
  &&  “ ((Zabs (gs)) <= gcap) ”
  &&  “ (gs = 1) ”
  &&  “ (1 <= G) ”
  &&  “ (G <= UINT_MAX) ”
  &&  (((gd + (0 * sizeof(UINT)))) # UInt  |-> G)
  **  (UIntArray.missing_i gd 0 0 1 (cons (G) ((@nil Z))) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> gs)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> gcap)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> gd)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
  **  (UIntArray.undef_seg gd (Zabs (gs)) gcap )
.

Definition normalize_partial_solve_wit_21_pure :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G)) (PreH13 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (( &( "tmp" ) ) <> 0)) (PreH15 : (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G )),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
.

Definition normalize_partial_solve_wit_21_aux :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G)) (PreH13 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (( &( "tmp" ) ) <> 0)) (PreH15 : (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G ) ”
  &&  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_21 := normalize_partial_solve_wit_21_pure -> normalize_partial_solve_wit_21_aux.

Definition normalize_partial_solve_wit_22 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (Rem: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 < G)) (PreH13 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH14 : (( &( "tmp" ) ) <> 0)) (PreH15 : (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G )),
  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row D_normalize_staged_row 0) G ) ”
  &&  (store_Z (DP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))) (Znth I_normalize_staged_row D_normalize_staged_row 0) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row D_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i DP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row D_normalize_staged_row )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row C_normalize_staged_row )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) A_normalize_staged_row )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_23 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (Rem: Z) (T: Z) (Aa: (@list Z)) (Ca: (@list Z)) (Da: (@list Z)) (G: Z) (slot: Z) (PreH1 : (slot <> (K_normalize_staged_row - M_normalize_staged_row ))) (PreH2 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH3 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH4 : (simplex_mpz_layout )) (PreH5 : (0 <= I_normalize_staged_row)) (PreH6 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH7 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH8 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH9 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH10 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : (K_normalize_staged_row < UINT_MAX)) (PreH12 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH13 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH14 : (0 <= slot)) (PreH15 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH16 : (0 < G)) (PreH17 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH18 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH19 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH20 : (Ca = C_normalize_staged_row)) (PreH21 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (slot <> (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  (((NP_normalize_staged_row + (slot * sizeof(UINT)))) # UInt  |-> (Znth slot N_normalize_staged_row 0))
  **  (UIntArray.missing_i NP_normalize_staged_row slot 0 (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_24 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (PreH1 : (j < K_normalize_staged_row)) (PreH2 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH3 : (simplex_mpz_layout )) (PreH4 : (0 <= I_normalize_staged_row)) (PreH5 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH6 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH7 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH8 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH9 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH10 : (K_normalize_staged_row < UINT_MAX)) (PreH11 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH13 : (0 <= slot)) (PreH14 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH15 : (0 < G)) (PreH16 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH17 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH18 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH19 : (Ca = C_normalize_staged_row)) (PreH20 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH21 : (0 <= slot)) (PreH22 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (j = (Znth slot N_normalize_staged_row 0))) (PreH24 : (0 <= j)) (PreH25 : (j < K_normalize_staged_row)) (PreH26 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (j < K_normalize_staged_row) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  (((RP_normalize_staged_row + (j * sizeof(UINT)))) # UInt  |-> (Znth j R_normalize_staged_row 0))
  **  (UIntArray.missing_i RP_normalize_staged_row j 0 K_normalize_staged_row R_normalize_staged_row )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_25 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH17 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH18 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH19 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH20 : (( &( "tmp" ) ) <> 0)) (PreH21 : (pivot_divides_exactly X G )) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z x X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row))) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0)) ”
  &&  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_26 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH17 : (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH18 : (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row)))) (PreH19 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH20 : (( &( "tmp" ) ) <> 0)) (PreH21 : (pivot_divides_exactly X G )) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z x X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot = ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (Ca = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row C_normalize_staged_row 0)) (G))) (C_normalize_staged_row))) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row Ca 0)) ”
  &&  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_27 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH17 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (Ca = C_normalize_staged_row)) (PreH19 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH20 : (( &( "tmp" ) ) <> 0)) (PreH21 : (pivot_divides_exactly X G )) (PreH22 : (0 <= slot)) (PreH23 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH24 : (j = (Znth slot N_normalize_staged_row 0))) (PreH25 : (0 <= j)) (PreH26 : (j < K_normalize_staged_row)) (PreH27 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH28 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH29 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z x X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0)) ”
  &&  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_28 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (PreH1 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH2 : (simplex_mpz_layout )) (PreH3 : (0 <= I_normalize_staged_row)) (PreH4 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH5 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH6 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH7 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH8 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH9 : (K_normalize_staged_row < UINT_MAX)) (PreH10 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH11 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH12 : (0 <= slot)) (PreH13 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH14 : (0 < G)) (PreH15 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH16 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH17 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH18 : (Ca = C_normalize_staged_row)) (PreH19 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH20 : (( &( "tmp" ) ) <> 0)) (PreH21 : (pivot_divides_exactly X G )) (PreH22 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH23 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH24 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (store_Z x X )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row Ca 0)) ”
  &&  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_29_pure :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
.

Definition normalize_partial_solve_wit_29_aux :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0)) ”
  &&  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_29 := normalize_partial_solve_wit_29_pure -> normalize_partial_solve_wit_29_aux.

Definition normalize_partial_solve_wit_30_pure :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "r" ) )) # UInt  |-> I_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  ((( &( "slot" ) )) # UInt  |-> slot)
  **  ((( &( "j" ) )) # UInt  |-> K_normalize_staged_row)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row Ca 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
.

Definition normalize_partial_solve_wit_30_aux :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca 0))),
  ((&((x)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (X)) (Zabs (size)) )
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((x)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ ((normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) <> 0) ”
  &&  “ (pivot_divides_exactly (Znth I_normalize_staged_row Ca 0) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) ”
  &&  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row Ca 0)) ”
  &&  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z x (Znth I_normalize_staged_row Ca 0) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_30 := normalize_partial_solve_wit_30_pure -> normalize_partial_solve_wit_30_aux.

Definition normalize_partial_solve_wit_31 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (j: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (0 <= slot)) (PreH26 : (slot < (K_normalize_staged_row - M_normalize_staged_row ))) (PreH27 : (j = (Znth slot N_normalize_staged_row 0))) (PreH28 : (0 <= j)) (PreH29 : (j < K_normalize_staged_row)) (PreH30 : ((Znth j R_normalize_staged_row 0) = UINT_MAX)) (PreH31 : (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" ))))) (PreH32 : (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0))),
  (store_Z ( &( "tmp" ) ) ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot < (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (j = (Znth slot N_normalize_staged_row 0)) ”
  &&  “ (0 <= j) ”
  &&  “ (j < K_normalize_staged_row) ”
  &&  “ ((Znth j R_normalize_staged_row 0) = UINT_MAX) ”
  &&  “ (x = (AP_normalize_staged_row + (((I_normalize_staged_row * K_normalize_staged_row ) + j ) * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + j ) Aa 0)) ”
  &&  (store_Z x (Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa 0) )
  **  (store_Z ( &( "tmp" ) ) ((Znth ((I_normalize_staged_row * K_normalize_staged_row ) + (Znth slot N_normalize_staged_row 0) ) Aa 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Ca )
  **  (MpzArray.missing_i AP_normalize_staged_row ((I_normalize_staged_row * K_normalize_staged_row ) + j ) 0 (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_32 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (Rem: Z) (X: Z) (Da: (@list Z)) (Ca: (@list Z)) (Aa: (@list Z)) (slot: Z) (x: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign X size )) (PreH3 : ((Zabs (size)) <= cap)) (PreH4 : (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) )) (PreH5 : (simplex_mpz_layout )) (PreH6 : (0 <= I_normalize_staged_row)) (PreH7 : (I_normalize_staged_row < M_normalize_staged_row)) (PreH8 : (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row )) (PreH9 : (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0))) (PreH10 : (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row )) (PreH11 : (0 <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH12 : (K_normalize_staged_row < UINT_MAX)) (PreH13 : ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH14 : ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row ))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 ))) (PreH17 : (0 < G)) (PreH18 : (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)))) (PreH19 : (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row)))) (PreH20 : (slot <= (K_normalize_staged_row - M_normalize_staged_row ))) (PreH21 : (Ca = C_normalize_staged_row)) (PreH22 : (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa )) (PreH23 : (( &( "tmp" ) ) <> 0)) (PreH24 : (pivot_divides_exactly X G )) (PreH25 : (slot = (K_normalize_staged_row - M_normalize_staged_row ))) (PreH26 : (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" ))))) (PreH27 : (X = (Znth I_normalize_staged_row Ca 0))),
  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row Ca 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z x (Znth I_normalize_staged_row Ca 0) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (size <> 0) ”
  &&  “ (same_sign X size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  “ (simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= I_normalize_staged_row) ”
  &&  “ (I_normalize_staged_row < M_normalize_staged_row) ”
  &&  “ (normalize_columns K_normalize_staged_row B_normalize_staged_row R_normalize_staged_row N_normalize_staged_row ) ”
  &&  “ (0 < (Znth I_normalize_staged_row D_normalize_staged_row 0)) ”
  &&  “ (normalize_basic_zero K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row B_normalize_staged_row ) ”
  &&  “ (0 <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (K_normalize_staged_row < UINT_MAX) ”
  &&  “ ((Zlength (N_normalize_staged_row)) = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ ((Zlength (A_normalize_staged_row)) = (M_normalize_staged_row * K_normalize_staged_row )) ”
  &&  “ (0 <= slot) ”
  &&  “ (slot <= ((K_normalize_staged_row - M_normalize_staged_row ) + 1 )) ”
  &&  “ (0 < G) ”
  &&  “ (G = (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row))) ”
  &&  “ (Da = (replace_Znth (I_normalize_staged_row) ((Z.quot ((Znth I_normalize_staged_row D_normalize_staged_row 0)) (G))) (D_normalize_staged_row))) ”
  &&  “ (slot <= (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (Ca = C_normalize_staged_row) ”
  &&  “ (normalize_coeff_prefix M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row G (Z.min (slot) ((K_normalize_staged_row - M_normalize_staged_row ))) A_normalize_staged_row N_normalize_staged_row Aa ) ”
  &&  “ (( &( "tmp" ) ) <> 0) ”
  &&  “ (pivot_divides_exactly X G ) ”
  &&  “ (slot = (K_normalize_staged_row - M_normalize_staged_row )) ”
  &&  “ (x = (CP_normalize_staged_row + (I_normalize_staged_row * sizeof( "__mpz_struct" )))) ”
  &&  “ (X = (Znth I_normalize_staged_row Ca 0)) ”
  &&  (store_Z x (Znth I_normalize_staged_row C_normalize_staged_row 0) )
  **  (store_Z ( &( "tmp" ) ) ((Znth I_normalize_staged_row C_normalize_staged_row 0) ÷ (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) ) )
  **  (store_Z ( &( "g" ) ) (normalize_row_gcd (K_normalize_staged_row) (I_normalize_staged_row) (D_normalize_staged_row) (C_normalize_staged_row) (A_normalize_staged_row) (N_normalize_staged_row)) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.missing_i CP_normalize_staged_row I_normalize_staged_row 0 M_normalize_staged_row Ca )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) Aa )
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Da )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "remainder" ) ) Rem )
.

Definition normalize_partial_solve_wit_33 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Rem: Z) (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)) (PreH1 : (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An )),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
  **  (store_Z ( &( "remainder" ) ) Rem )
|--
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  (store_Z ( &( "remainder" ) ) Rem )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
.

Definition normalize_partial_solve_wit_34 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (G: Z) (T: Z) (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An )),
  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "g" ) ) G )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  (store_Z ( &( "g" ) ) G )
  **  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
.

Definition normalize_partial_solve_wit_35 :=
forall (N_normalize_staged_row: (@list Z)) (R_normalize_staged_row: (@list Z)) (B_normalize_staged_row: (@list Z)) (A_normalize_staged_row: (@list Z)) (C_normalize_staged_row: (@list Z)) (D_normalize_staged_row: (@list Z)) (NP_normalize_staged_row: Z) (RP_normalize_staged_row: Z) (BP_normalize_staged_row: Z) (AP_normalize_staged_row: Z) (CP_normalize_staged_row: Z) (DP_normalize_staged_row: Z) (I_normalize_staged_row: Z) (K_normalize_staged_row: Z) (M_normalize_staged_row: Z) (t_pre: Z) (T: Z) (Dn: (@list Z)) (Cn: (@list Z)) (An: (@list Z)) (ptr: Z) (cap: Z) (size: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) (PreH1 : (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An )),
  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
  **  (store_Z ( &( "tmp" ) ) T )
|--
  “ (normalize_result M_normalize_staged_row K_normalize_staged_row I_normalize_staged_row D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row N_normalize_staged_row Dn Cn An ) ”
  &&  (store_Z ( &( "tmp" ) ) T )
  **  ((&(( &( "g" ) )->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&(( &( "g" ) )->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_size")) # Int  |-> size)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&(( &( "remainder" ) )->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> K_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_normalize_staged_row)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_normalize_staged_row)
  **  (MpzArray.full DP_normalize_staged_row M_normalize_staged_row Dn )
  **  (MpzArray.full CP_normalize_staged_row M_normalize_staged_row Cn )
  **  (MpzArray.full AP_normalize_staged_row (M_normalize_staged_row * K_normalize_staged_row ) An )
  **  (UIntArray.full BP_normalize_staged_row M_normalize_staged_row B_normalize_staged_row )
  **  (UIntArray.full RP_normalize_staged_row K_normalize_staged_row R_normalize_staged_row )
  **  (UIntArray.full NP_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row ) N_normalize_staged_row )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_normalize_safety_wit_1 : normalize_safety_wit_1.
Axiom proof_of_normalize_safety_wit_2 : normalize_safety_wit_2.
Axiom proof_of_normalize_safety_wit_3 : normalize_safety_wit_3.
Axiom proof_of_normalize_safety_wit_4 : normalize_safety_wit_4.
Axiom proof_of_normalize_safety_wit_5 : normalize_safety_wit_5.
Axiom proof_of_normalize_safety_wit_6 : normalize_safety_wit_6.
Axiom proof_of_normalize_safety_wit_7 : normalize_safety_wit_7.
Axiom proof_of_normalize_safety_wit_8 : normalize_safety_wit_8.
Axiom proof_of_normalize_safety_wit_9 : normalize_safety_wit_9.
Axiom proof_of_normalize_safety_wit_10 : normalize_safety_wit_10.
Axiom proof_of_normalize_safety_wit_11 : normalize_safety_wit_11.
Axiom proof_of_normalize_safety_wit_12 : normalize_safety_wit_12.
Axiom proof_of_normalize_safety_wit_13 : normalize_safety_wit_13.
Axiom proof_of_normalize_safety_wit_14 : normalize_safety_wit_14.
Axiom proof_of_normalize_safety_wit_15 : normalize_safety_wit_15.
Axiom proof_of_normalize_safety_wit_16 : normalize_safety_wit_16.
Axiom proof_of_normalize_safety_wit_17 : normalize_safety_wit_17.
Axiom proof_of_normalize_safety_wit_18 : normalize_safety_wit_18.
Axiom proof_of_normalize_safety_wit_19 : normalize_safety_wit_19.
Axiom proof_of_normalize_safety_wit_20 : normalize_safety_wit_20.
Axiom proof_of_normalize_safety_wit_21 : normalize_safety_wit_21.
Axiom proof_of_normalize_safety_wit_22 : normalize_safety_wit_22.
Axiom proof_of_normalize_safety_wit_23 : normalize_safety_wit_23.
Axiom proof_of_normalize_safety_wit_24 : normalize_safety_wit_24.
Axiom proof_of_normalize_safety_wit_25 : normalize_safety_wit_25.
Axiom proof_of_normalize_safety_wit_26 : normalize_safety_wit_26.
Axiom proof_of_normalize_safety_wit_27 : normalize_safety_wit_27.
Axiom proof_of_normalize_safety_wit_28 : normalize_safety_wit_28.
Axiom proof_of_normalize_safety_wit_29 : normalize_safety_wit_29.
Axiom proof_of_normalize_safety_wit_30 : normalize_safety_wit_30.
Axiom proof_of_normalize_safety_wit_31 : normalize_safety_wit_31.
Axiom proof_of_normalize_safety_wit_32 : normalize_safety_wit_32.
Axiom proof_of_normalize_safety_wit_33 : normalize_safety_wit_33.
Axiom proof_of_normalize_safety_wit_34 : normalize_safety_wit_34.
Axiom proof_of_normalize_safety_wit_35 : normalize_safety_wit_35.
Axiom proof_of_normalize_safety_wit_36 : normalize_safety_wit_36.
Axiom proof_of_normalize_safety_wit_37 : normalize_safety_wit_37.
Axiom proof_of_normalize_safety_wit_38 : normalize_safety_wit_38.
Axiom proof_of_normalize_safety_wit_39 : normalize_safety_wit_39.
Axiom proof_of_normalize_safety_wit_40 : normalize_safety_wit_40.
Axiom proof_of_normalize_safety_wit_41 : normalize_safety_wit_41.
Axiom proof_of_normalize_safety_wit_42 : normalize_safety_wit_42.
Axiom proof_of_normalize_safety_wit_43 : normalize_safety_wit_43.
Axiom proof_of_normalize_safety_wit_44 : normalize_safety_wit_44.
Axiom proof_of_normalize_safety_wit_45 : normalize_safety_wit_45.
Axiom proof_of_normalize_safety_wit_46 : normalize_safety_wit_46.
Axiom proof_of_normalize_safety_wit_47 : normalize_safety_wit_47.
Axiom proof_of_normalize_safety_wit_48 : normalize_safety_wit_48.
Axiom proof_of_normalize_safety_wit_49 : normalize_safety_wit_49.
Axiom proof_of_normalize_safety_wit_50 : normalize_safety_wit_50.
Axiom proof_of_normalize_entail_wit_1 : normalize_entail_wit_1.
Axiom proof_of_normalize_entail_wit_2 : normalize_entail_wit_2.
Axiom proof_of_normalize_entail_wit_3_1 : normalize_entail_wit_3_1.
Axiom proof_of_normalize_entail_wit_3_2 : normalize_entail_wit_3_2.
Axiom proof_of_normalize_entail_wit_4_1 : normalize_entail_wit_4_1.
Axiom proof_of_normalize_entail_wit_4_2 : normalize_entail_wit_4_2.
Axiom proof_of_normalize_entail_wit_4_3 : normalize_entail_wit_4_3.
Axiom proof_of_normalize_entail_wit_4_4 : normalize_entail_wit_4_4.
Axiom proof_of_normalize_entail_wit_5_1 : normalize_entail_wit_5_1.
Axiom proof_of_normalize_entail_wit_5_2 : normalize_entail_wit_5_2.
Axiom proof_of_normalize_entail_wit_5_3 : normalize_entail_wit_5_3.
Axiom proof_of_normalize_entail_wit_5_4 : normalize_entail_wit_5_4.
Axiom proof_of_normalize_entail_wit_5_5 : normalize_entail_wit_5_5.
Axiom proof_of_normalize_entail_wit_5_6 : normalize_entail_wit_5_6.
Axiom proof_of_normalize_entail_wit_6_1 : normalize_entail_wit_6_1.
Axiom proof_of_normalize_entail_wit_6_2 : normalize_entail_wit_6_2.
Axiom proof_of_normalize_entail_wit_6_3 : normalize_entail_wit_6_3.
Axiom proof_of_normalize_entail_wit_7_1 : normalize_entail_wit_7_1.
Axiom proof_of_normalize_entail_wit_7_2 : normalize_entail_wit_7_2.
Axiom proof_of_normalize_entail_wit_8 : normalize_entail_wit_8.
Axiom proof_of_normalize_entail_wit_9_1 : normalize_entail_wit_9_1.
Axiom proof_of_normalize_entail_wit_9_2 : normalize_entail_wit_9_2.
Axiom proof_of_normalize_entail_wit_10_1 : normalize_entail_wit_10_1.
Axiom proof_of_normalize_entail_wit_10_2 : normalize_entail_wit_10_2.
Axiom proof_of_normalize_entail_wit_11_1 : normalize_entail_wit_11_1.
Axiom proof_of_normalize_entail_wit_11_2 : normalize_entail_wit_11_2.
Axiom proof_of_normalize_entail_wit_11_3 : normalize_entail_wit_11_3.
Axiom proof_of_normalize_entail_wit_11_4 : normalize_entail_wit_11_4.
Axiom proof_of_normalize_entail_wit_12_1 : normalize_entail_wit_12_1.
Axiom proof_of_normalize_entail_wit_12_2 : normalize_entail_wit_12_2.
Axiom proof_of_normalize_return_wit_1 : normalize_return_wit_1.
Axiom proof_of_normalize_partial_solve_wit_1 : normalize_partial_solve_wit_1.
Axiom proof_of_normalize_partial_solve_wit_2 : normalize_partial_solve_wit_2.
Axiom proof_of_normalize_partial_solve_wit_3 : normalize_partial_solve_wit_3.
Axiom proof_of_normalize_partial_solve_wit_4 : normalize_partial_solve_wit_4.
Axiom proof_of_normalize_partial_solve_wit_5 : normalize_partial_solve_wit_5.
Axiom proof_of_normalize_partial_solve_wit_6 : normalize_partial_solve_wit_6.
Axiom proof_of_normalize_partial_solve_wit_7 : normalize_partial_solve_wit_7.
Axiom proof_of_normalize_partial_solve_wit_8 : normalize_partial_solve_wit_8.
Axiom proof_of_normalize_partial_solve_wit_9 : normalize_partial_solve_wit_9.
Axiom proof_of_normalize_partial_solve_wit_10 : normalize_partial_solve_wit_10.
Axiom proof_of_normalize_partial_solve_wit_11 : normalize_partial_solve_wit_11.
Axiom proof_of_normalize_partial_solve_wit_12_pure : normalize_partial_solve_wit_12_pure.
Axiom proof_of_normalize_partial_solve_wit_12 : normalize_partial_solve_wit_12.
Axiom proof_of_normalize_partial_solve_wit_13_pure : normalize_partial_solve_wit_13_pure.
Axiom proof_of_normalize_partial_solve_wit_13 : normalize_partial_solve_wit_13.
Axiom proof_of_normalize_partial_solve_wit_14 : normalize_partial_solve_wit_14.
Axiom proof_of_normalize_partial_solve_wit_15 : normalize_partial_solve_wit_15.
Axiom proof_of_normalize_partial_solve_wit_16 : normalize_partial_solve_wit_16.
Axiom proof_of_normalize_partial_solve_wit_17 : normalize_partial_solve_wit_17.
Axiom proof_of_normalize_partial_solve_wit_18 : normalize_partial_solve_wit_18.
Axiom proof_of_normalize_partial_solve_wit_19 : normalize_partial_solve_wit_19.
Axiom proof_of_normalize_partial_solve_wit_20 : normalize_partial_solve_wit_20.
Axiom proof_of_normalize_partial_solve_wit_21_pure : normalize_partial_solve_wit_21_pure.
Axiom proof_of_normalize_partial_solve_wit_21 : normalize_partial_solve_wit_21.
Axiom proof_of_normalize_partial_solve_wit_22 : normalize_partial_solve_wit_22.
Axiom proof_of_normalize_partial_solve_wit_23 : normalize_partial_solve_wit_23.
Axiom proof_of_normalize_partial_solve_wit_24 : normalize_partial_solve_wit_24.
Axiom proof_of_normalize_partial_solve_wit_25 : normalize_partial_solve_wit_25.
Axiom proof_of_normalize_partial_solve_wit_26 : normalize_partial_solve_wit_26.
Axiom proof_of_normalize_partial_solve_wit_27 : normalize_partial_solve_wit_27.
Axiom proof_of_normalize_partial_solve_wit_28 : normalize_partial_solve_wit_28.
Axiom proof_of_normalize_partial_solve_wit_29_pure : normalize_partial_solve_wit_29_pure.
Axiom proof_of_normalize_partial_solve_wit_29 : normalize_partial_solve_wit_29.
Axiom proof_of_normalize_partial_solve_wit_30_pure : normalize_partial_solve_wit_30_pure.
Axiom proof_of_normalize_partial_solve_wit_30 : normalize_partial_solve_wit_30.
Axiom proof_of_normalize_partial_solve_wit_31 : normalize_partial_solve_wit_31.
Axiom proof_of_normalize_partial_solve_wit_32 : normalize_partial_solve_wit_32.
Axiom proof_of_normalize_partial_solve_wit_33 : normalize_partial_solve_wit_33.
Axiom proof_of_normalize_partial_solve_wit_34 : normalize_partial_solve_wit_34.
Axiom proof_of_normalize_partial_solve_wit_35 : normalize_partial_solve_wit_35.

End VC_Correct.
