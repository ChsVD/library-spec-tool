From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.destroy_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function destroy -----*)

Definition destroy_entail_wit_1 :=
(
forall (AV_destroy_owned_table: (@list Z)) (CV_destroy_owned_table: (@list Z)) (DV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols_2)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token DP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full DP_destroy_owned_table M_destroy_owned_table DV_destroy_owned_table )
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  EX (t_cols: Z),
  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token DP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full DP_destroy_owned_table M_destroy_owned_table DV_destroy_owned_table )
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
) \/
(
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  TT && emp 
|--
  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  emp
).

Definition destroy_entail_wit_1_split_goal_1 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)
.

Definition destroy_entail_wit_1_split_goal_2 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))
.

Definition destroy_entail_wit_1_split_goal_3 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)
.

Definition destroy_entail_wit_1_split_goal_4 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))
.

Definition destroy_entail_wit_1_split_goal_5 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))
.

Definition destroy_entail_wit_1_split_goal_6 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)
.

Definition destroy_entail_wit_1_split_goal_7 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))
.

Definition destroy_entail_wit_1_split_goal_8 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (0 <= N_destroy_owned_table)
.

Definition destroy_entail_wit_1_split_goal_9 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (M_destroy_owned_table <= INT_MAX)
.

Definition destroy_entail_wit_1_split_goal_10 :=
forall (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (simplex_dimensions_ok M_destroy_owned_table N_destroy_owned_table )) (PreH3 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))),
  (0 <= M_destroy_owned_table)
.

Definition destroy_return_wit_1 :=
forall (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols_2: Z) (PreH1 : (t_cols_2 = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols_2)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
|--
  EX (t_cols: Z),
  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |->_)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |->_)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |->_)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |->_)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |->_)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |->_)
.

Definition destroy_partial_solve_wit_1_pure :=
forall (AV_destroy_owned_table: (@list Z)) (CV_destroy_owned_table: (@list Z)) (DV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token DP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full DP_destroy_owned_table M_destroy_owned_table DV_destroy_owned_table )
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition destroy_partial_solve_wit_1_aux :=
forall (AV_destroy_owned_table: (@list Z)) (CV_destroy_owned_table: (@list Z)) (DV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token DP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full DP_destroy_owned_table M_destroy_owned_table DV_destroy_owned_table )
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  (simplex_malloc_token DP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full DP_destroy_owned_table M_destroy_owned_table DV_destroy_owned_table )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
.

Definition destroy_partial_solve_wit_1 := destroy_partial_solve_wit_1_pure -> destroy_partial_solve_wit_1_aux.

Definition destroy_partial_solve_wit_2_pure :=
forall (AV_destroy_owned_table: (@list Z)) (CV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition destroy_partial_solve_wit_2_aux :=
forall (AV_destroy_owned_table: (@list Z)) (CV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  (simplex_malloc_token CP_destroy_owned_table (M_destroy_owned_table * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP_destroy_owned_table M_destroy_owned_table CV_destroy_owned_table )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
.

Definition destroy_partial_solve_wit_2 := destroy_partial_solve_wit_2_pure -> destroy_partial_solve_wit_2_aux.

Definition destroy_partial_solve_wit_3_pure :=
forall (AV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (0 <= (M_destroy_owned_table * t_cols )) ”
  &&  “ ((M_destroy_owned_table * t_cols ) <= INT_MAX) ”
  &&  “ ((0 < (M_destroy_owned_table * t_cols )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= ((M_destroy_owned_table * t_cols ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * t_cols ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition destroy_partial_solve_wit_3_aux :=
forall (AV_destroy_owned_table: (@list Z)) (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) AV_destroy_owned_table )
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (0 <= (M_destroy_owned_table * t_cols )) ”
  &&  “ ((M_destroy_owned_table * t_cols ) <= INT_MAX) ”
  &&  “ ((0 < (M_destroy_owned_table * t_cols )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= ((M_destroy_owned_table * t_cols ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * t_cols ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  (simplex_malloc_token AP_destroy_owned_table ((M_destroy_owned_table * t_cols ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP_destroy_owned_table (M_destroy_owned_table * t_cols ) AV_destroy_owned_table )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
.

Definition destroy_partial_solve_wit_3 := destroy_partial_solve_wit_3_pure -> destroy_partial_solve_wit_3_aux.

Definition destroy_partial_solve_wit_4 :=
forall (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  (simplex_malloc_token BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP_destroy_owned_table (M_destroy_owned_table * sizeof(UINT) ) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
.

Definition destroy_partial_solve_wit_5 :=
forall (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  (simplex_malloc_token RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_destroy_owned_table ((M_destroy_owned_table + N_destroy_owned_table ) * sizeof(UINT) ) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
.

Definition destroy_partial_solve_wit_6 :=
forall (NP_destroy_owned_table: Z) (RP_destroy_owned_table: Z) (BP_destroy_owned_table: Z) (AP_destroy_owned_table: Z) (CP_destroy_owned_table: Z) (DP_destroy_owned_table: Z) (N_destroy_owned_table: Z) (M_destroy_owned_table: Z) (t_pre: Z) (t_cols: Z) (PreH1 : (t_cols = (M_destroy_owned_table + N_destroy_owned_table ))) (PreH2 : (0 <= M_destroy_owned_table)) (PreH3 : (M_destroy_owned_table <= INT_MAX)) (PreH4 : (0 <= N_destroy_owned_table)) (PreH5 : (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ))) (PreH6 : ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX)) (PreH7 : ((0 < M_destroy_owned_table) -> (simplex_mpz_layout ))) (PreH8 : ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout ))) (PreH9 : (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) ))) (PreH10 : ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX)) (PreH11 : (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ))) (PreH12 : (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX)),
  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
  **  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
|--
  “ (t_cols = (M_destroy_owned_table + N_destroy_owned_table )) ”
  &&  “ (0 <= M_destroy_owned_table) ”
  &&  “ (M_destroy_owned_table <= INT_MAX) ”
  &&  “ (0 <= N_destroy_owned_table) ”
  &&  “ (0 <= (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) ”
  &&  “ ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) <= INT_MAX) ”
  &&  “ ((0 < M_destroy_owned_table) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) )) -> (simplex_mpz_layout )) ”
  &&  “ (0 <= (M_destroy_owned_table * sizeof( "__mpz_struct" ) )) ”
  &&  “ ((M_destroy_owned_table * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= ((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) )) ”
  &&  “ (((M_destroy_owned_table * (M_destroy_owned_table + N_destroy_owned_table ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  (simplex_malloc_token NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_destroy_owned_table (N_destroy_owned_table * sizeof(UINT) ) )
  **  ((&((t_pre)  # "table" ->ₛ "rows")) # UInt  |-> M_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "cols")) # UInt  |-> t_cols)
  **  ((&((t_pre)  # "table" ->ₛ "d")) # Ptr  |-> DP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "c")) # Ptr  |-> CP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "a")) # Ptr  |-> AP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "basic")) # Ptr  |-> BP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "row")) # Ptr  |-> RP_destroy_owned_table)
  **  ((&((t_pre)  # "table" ->ₛ "nonbasic")) # Ptr  |-> NP_destroy_owned_table)
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_destroy_entail_wit_1 : destroy_entail_wit_1.
Axiom proof_of_destroy_return_wit_1 : destroy_return_wit_1.
Axiom proof_of_destroy_partial_solve_wit_1_pure : destroy_partial_solve_wit_1_pure.
Axiom proof_of_destroy_partial_solve_wit_1 : destroy_partial_solve_wit_1.
Axiom proof_of_destroy_partial_solve_wit_2_pure : destroy_partial_solve_wit_2_pure.
Axiom proof_of_destroy_partial_solve_wit_2 : destroy_partial_solve_wit_2.
Axiom proof_of_destroy_partial_solve_wit_3_pure : destroy_partial_solve_wit_3_pure.
Axiom proof_of_destroy_partial_solve_wit_3 : destroy_partial_solve_wit_3.
Axiom proof_of_destroy_partial_solve_wit_4 : destroy_partial_solve_wit_4.
Axiom proof_of_destroy_partial_solve_wit_5 : destroy_partial_solve_wit_5.
Axiom proof_of_destroy_partial_solve_wit_6 : destroy_partial_solve_wit_6.

End VC_Correct.
