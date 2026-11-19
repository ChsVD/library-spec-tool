From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.mpz_tdiv_r_sep_opt_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.

(*----- Function mpz_tdiv_r -----*)

Definition mpz_tdiv_r_safety_wit_1 :=
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_tdiv_r_safety_wit_2 :=
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpz_tdiv_r_entail_wit_1 :=
(
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
|--
  “ (r_pre <> 0) ”
  &&  “ (zd_separated_trunc <> 0) ”
  &&  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
) \/
(
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
|--
  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
).

Definition mpz_tdiv_r_entail_wit_1_split_goal_spatial :=
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
|--
  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
.

Definition mpz_tdiv_r_return_wit_1 :=
(
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn_separated_trunc zd_separated_trunc qv rv )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv )) (PreH5 : (r_pre <> 0)) (PreH6 : (zd_separated_trunc <> 0)),
  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 qv )
  **  (optional_store_Z r_pre rv )
|--
  (store_Z r_pre (Z.rem (zn_separated_trunc) (zd_separated_trunc)) )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
) \/
(
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn_separated_trunc zd_separated_trunc qv rv )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv )) (PreH5 : (r_pre <> 0)) (PreH6 : (zd_separated_trunc <> 0)),
  (store_Z r_pre rv )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 qv )
|--
  (store_Z r_pre (Z.rem (zn_separated_trunc) (zd_separated_trunc)) )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
).

Definition mpz_tdiv_r_return_wit_1_split_goal_spatial :=
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (qv: Z) (rv: Z) (retval: Z) (PreH1 : (mpz_div_qr_math 2 zn_separated_trunc zd_separated_trunc qv rv )) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (mpz_div_qr_ret_ok retval rv )) (PreH5 : (r_pre <> 0)) (PreH6 : (zd_separated_trunc <> 0)),
  (store_Z r_pre rv )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 qv )
|--
  (store_Z r_pre (Z.rem (zn_separated_trunc) (zd_separated_trunc)) )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
.

Definition mpz_tdiv_r_partial_solve_wit_1_pure :=
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
|--
  “ (0 = 0) ”
  &&  “ (r_pre = r_pre) ”
  &&  “ (n_pre = n_pre) ”
  &&  “ (d_pre = d_pre) ”
  &&  “ (2 = 2) ”
  &&  “ (zd_separated_trunc <> 0) ”
  &&  “ (2 = 2) ”
.

Definition mpz_tdiv_r_partial_solve_wit_1_aux :=
forall (zd_separated_trunc: Z) (zn_separated_trunc: Z) (old_separated_trunc: Z) (r_pre: Z) (n_pre: Z) (d_pre: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (zd_separated_trunc <> 0)),
  (store_Z r_pre old_separated_trunc )
  **  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
|--
  “ (0 = 0) ”
  &&  “ (r_pre = r_pre) ”
  &&  “ (n_pre = n_pre) ”
  &&  “ (d_pre = d_pre) ”
  &&  “ (2 = 2) ”
  &&  “ (zd_separated_trunc <> 0) ”
  &&  “ (2 = 2) ”
  &&  “ (r_pre <> 0) ”
  &&  “ (zd_separated_trunc <> 0) ”
  &&  (store_Z n_pre zn_separated_trunc )
  **  (store_Z d_pre zd_separated_trunc )
  **  (optional_store_Z 0 0 )
  **  (optional_store_Z r_pre old_separated_trunc )
.

Definition mpz_tdiv_r_partial_solve_wit_1 := mpz_tdiv_r_partial_solve_wit_1_pure -> mpz_tdiv_r_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpz_tdiv_r_safety_wit_1 : mpz_tdiv_r_safety_wit_1.
Axiom proof_of_mpz_tdiv_r_safety_wit_2 : mpz_tdiv_r_safety_wit_2.
Axiom proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Axiom proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_1_pure : mpz_tdiv_r_partial_solve_wit_1_pure.
Axiom proof_of_mpz_tdiv_r_partial_solve_wit_1 : mpz_tdiv_r_partial_solve_wit_1.

End VC_Correct.
