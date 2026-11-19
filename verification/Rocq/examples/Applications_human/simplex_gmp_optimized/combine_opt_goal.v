From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function combine -----*)

Definition combine_safety_wit_1 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign A_non_alias size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition combine_safety_wit_2 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign B_non_alias size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (size = 0)) (PreH4 : (same_sign A_non_alias size )) (PreH5 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition combine_safety_wit_3 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition combine_safety_wit_4 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (same_sign M_non_alias msize )) (PreH2 : ((Zabs (msize)) <= cap)) (PreH3 : (msize = 1)) (PreH4 : (1 <= M_non_alias)) (PreH5 : (M_non_alias <= UINT_MAX)),
  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr 1 (cons (M_non_alias) ((@nil Z))) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition combine_safety_wit_5 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (same_sign M_non_alias msize )) (PreH2 : ((Zabs (msize)) <= cap)) (PreH3 : (msize <> 1)),
  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition combine_safety_wit_6 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (msize <> 1)) (PreH2 : (same_sign M_non_alias msize )) (PreH3 : ((Zabs (msize)) <= cap)) (PreH4 : (msize = 1)) (PreH5 : (1 <= M_non_alias)) (PreH6 : (M_non_alias <= UINT_MAX)),
  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr 1 (cons (M_non_alias) ((@nil Z))) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ False ”
.

Definition combine_safety_wit_7 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (msize = 1)) (PreH2 : (same_sign M_non_alias msize )) (PreH3 : ((Zabs (msize)) <= cap)) (PreH4 : (msize <> 1)),
  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ False ”
.

Definition combine_safety_wit_8 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (msize = 1)) (PreH2 : (same_sign M_non_alias msize )) (PreH3 : ((Zabs (msize)) <= cap)) (PreH4 : (msize = 1)) (PreH5 : (1 <= M_non_alias)) (PreH6 : (M_non_alias <= UINT_MAX)),
  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr 1 (cons (M_non_alias) ((@nil Z))) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition combine_safety_wit_9 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (msize = 1)) (PreH2 : (same_sign M_non_alias msize )) (PreH3 : ((Zabs (msize)) <= cap)) (PreH4 : (msize = 1)) (PreH5 : (1 <= M_non_alias)) (PreH6 : (M_non_alias <= UINT_MAX)),
  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition combine_safety_wit_10 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (same_sign B_non_alias size )) (PreH2 : ((Zabs (size)) <= cap_2)) (PreH3 : (M_non_alias = 1)) (PreH4 : (msize = 1)) (PreH5 : (same_sign M_non_alias msize )) (PreH6 : ((Zabs (msize)) <= cap)) (PreH7 : (msize = 1)) (PreH8 : (1 <= M_non_alias)) (PreH9 : (M_non_alias <= UINT_MAX)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z n_pre N_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition combine_safety_wit_11 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (same_sign B_non_alias size )) (PreH2 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z n_pre N_non_alias )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition combine_entail_wit_1 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign A_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  (EX (ptr: Z) (cap: Z) (msize: Z),
  “ (same_sign M_non_alias msize ) ”
  &&  “ ((Zabs (msize)) <= cap) ”
  &&  “ (msize <> 1) ”
  &&  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias ))
  ||
  (EX (ptr: Z) (cap: Z) (msize: Z),
  “ (same_sign M_non_alias msize ) ”
  &&  “ ((Zabs (msize)) <= cap) ”
  &&  “ (msize = 1) ”
  &&  “ (1 <= M_non_alias) ”
  &&  “ (M_non_alias <= UINT_MAX) ”
  &&  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr 1 (cons (M_non_alias) ((@nil Z))) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias ))
.

Definition combine_entail_wit_2_1 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (msize <> 1)) (PreH2 : (same_sign M_non_alias msize )) (PreH3 : ((Zabs (msize)) <= cap)) (PreH4 : (msize <> 1)),
  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_entail_wit_2_2 :=
(
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (M_non_alias <> 1)) (PreH2 : (msize = 1)) (PreH3 : (same_sign M_non_alias msize )) (PreH4 : ((Zabs (msize)) <= cap)) (PreH5 : (msize = 1)) (PreH6 : (1 <= M_non_alias)) (PreH7 : (M_non_alias <= UINT_MAX)),
  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
) \/
(
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (M_non_alias <> 1)) (PreH2 : (msize = 1)) (PreH3 : (same_sign M_non_alias msize )) (PreH4 : ((Zabs (msize)) <= cap)) (PreH5 : (msize = 1)) (PreH6 : (1 <= M_non_alias)) (PreH7 : (M_non_alias <= UINT_MAX)),
  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
).

Definition combine_entail_wit_2_2_split_goal_spatial :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (M_non_alias <> 1)) (PreH2 : (msize = 1)) (PreH3 : (same_sign M_non_alias msize )) (PreH4 : ((Zabs (msize)) <= cap)) (PreH5 : (msize = 1)) (PreH6 : (1 <= M_non_alias)) (PreH7 : (M_non_alias <= UINT_MAX)),
  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_return_wit_1 :=
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  (store_Z out_pre 0 )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (n_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  (store_Z out_pre 0 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
).

Definition combine_return_wit_1_split_goal_spatial :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (n_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  (store_Z out_pre 0 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_return_wit_2 :=
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  (store_Z out_pre (N_non_alias * B_non_alias ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z m_pre M_non_alias )
|--
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  (store_Z out_pre (N_non_alias * B_non_alias ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z m_pre M_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
).

Definition combine_return_wit_2_split_goal_spatial :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  (store_Z out_pre (N_non_alias * B_non_alias ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z m_pre M_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_return_wit_3 :=
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (size: Z) (cap_2: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  (store_Z out_pre (A_non_alias + (N_non_alias * B_non_alias ) ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
|--
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (size: Z) (cap_2: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  (store_Z out_pre (A_non_alias + (N_non_alias * B_non_alias ) ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
).

Definition combine_return_wit_3_split_goal_spatial :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (size: Z) (cap_2: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  (store_Z out_pre (A_non_alias + (N_non_alias * B_non_alias ) ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_return_wit_4 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
|--
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_return_wit_5 :=
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z n_pre N_non_alias )
|--
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (a_pre: Z) (n_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  (store_Z n_pre N_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
).

Definition combine_return_wit_5_split_goal_spatial :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (a_pre: Z) (n_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  (store_Z n_pre N_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (M_non_alias)) (Zabs (msize)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_return_wit_6 :=
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
) \/
(
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
).

Definition combine_return_wit_6_split_goal_spatial :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  (store_Z out_pre ((M_non_alias * A_non_alias ) + (N_non_alias * B_non_alias ) ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_partial_solve_wit_1 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z),
  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign A_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_partial_solve_wit_2 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (same_sign A_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  EX (ptr_2: Z) (size_2: Z) (cap_2: Z),
  “ (same_sign B_non_alias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size = 0) ”
  &&  “ (same_sign A_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_partial_solve_wit_3_pure :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "m" ) )) # Ptr  |-> m_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  “ (0 = 0) ”
  &&  “ (0 <= 0) ”
.

Definition combine_partial_solve_wit_3_aux :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 = 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  “ (0 = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (size_2 = 0) ”
  &&  “ (same_sign B_non_alias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size = 0) ”
  &&  “ (same_sign A_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z out_pre O_non_alias )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_partial_solve_wit_3 := combine_partial_solve_wit_3_pure -> combine_partial_solve_wit_3_aux.

Definition combine_partial_solve_wit_4 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (size_2 <> 0)) (PreH2 : (same_sign B_non_alias size_2 )) (PreH3 : ((Zabs (size_2)) <= cap_2)) (PreH4 : (size = 0)) (PreH5 : (same_sign A_non_alias size )) (PreH6 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size_2)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size_2)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  “ (size_2 <> 0) ”
  &&  “ (same_sign B_non_alias size_2 ) ”
  &&  “ ((Zabs (size_2)) <= cap_2) ”
  &&  “ (size = 0) ”
  &&  “ (same_sign A_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z out_pre O_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (A_non_alias)) (Zabs (size)) )
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((a_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z m_pre M_non_alias )
.

Definition combine_partial_solve_wit_5 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (msize = 1)) (PreH2 : (same_sign M_non_alias msize )) (PreH3 : ((Zabs (msize)) <= cap)) (PreH4 : (msize = 1)) (PreH5 : (1 <= M_non_alias)) (PreH6 : (M_non_alias <= UINT_MAX)),
  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.full ptr 1 (cons (M_non_alias) ((@nil Z))) )
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (msize = 1) ”
  &&  “ (same_sign M_non_alias msize ) ”
  &&  “ ((Zabs (msize)) <= cap) ”
  &&  “ (msize = 1) ”
  &&  “ (1 <= M_non_alias) ”
  &&  “ (M_non_alias <= UINT_MAX) ”
  &&  (((ptr + (0 * sizeof(UINT)))) # UInt  |-> M_non_alias)
  **  (UIntArray.missing_i ptr 0 0 1 (cons (M_non_alias) ((@nil Z))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_partial_solve_wit_6 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (M_non_alias = 1)) (PreH2 : (msize = 1)) (PreH3 : (same_sign M_non_alias msize )) (PreH4 : ((Zabs (msize)) <= cap)) (PreH5 : (msize = 1)) (PreH6 : (1 <= M_non_alias)) (PreH7 : (M_non_alias <= UINT_MAX)),
  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  “ (M_non_alias = 1) ”
  &&  “ (msize = 1) ”
  &&  “ (same_sign M_non_alias msize ) ”
  &&  “ ((Zabs (msize)) <= cap) ”
  &&  “ (msize = 1) ”
  &&  “ (1 <= M_non_alias) ”
  &&  “ (M_non_alias <= UINT_MAX) ”
  &&  (store_Z out_pre O_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_partial_solve_wit_7 :=
forall (O_non_alias: Z) (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z),
  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  (store_Z out_pre O_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
.

Definition combine_partial_solve_wit_8 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (PreH1 : (M_non_alias = 1)) (PreH2 : (msize = 1)) (PreH3 : (same_sign M_non_alias msize )) (PreH4 : ((Zabs (msize)) <= cap)) (PreH5 : (msize = 1)) (PreH6 : (1 <= M_non_alias)) (PreH7 : (M_non_alias <= UINT_MAX)),
  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  EX (ptr_2: Z) (size: Z) (cap_2: Z),
  “ (same_sign B_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap_2) ”
  &&  “ (M_non_alias = 1) ”
  &&  “ (msize = 1) ”
  &&  “ (same_sign M_non_alias msize ) ”
  &&  “ ((Zabs (msize)) <= cap) ”
  &&  “ (msize = 1) ”
  &&  “ (1 <= M_non_alias) ”
  &&  “ (M_non_alias <= UINT_MAX) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_partial_solve_wit_9 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z),
  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
|--
  EX (ptr: Z) (size: Z) (cap: Z),
  “ (same_sign B_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
.

Definition combine_partial_solve_wit_10 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (msize: Z) (cap: Z) (ptr_2: Z) (size: Z) (cap_2: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap_2)) (PreH4 : (M_non_alias = 1)) (PreH5 : (msize = 1)) (PreH6 : (same_sign M_non_alias msize )) (PreH7 : ((Zabs (msize)) <= cap)) (PreH8 : (msize = 1)) (PreH9 : (1 <= M_non_alias)) (PreH10 : (M_non_alias <= UINT_MAX)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr_2 (Zabs (size)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  (store_Z out_pre A_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
  **  (store_Z n_pre N_non_alias )
|--
  “ (size <> 0) ”
  &&  “ (same_sign B_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap_2) ”
  &&  “ (M_non_alias = 1) ”
  &&  “ (msize = 1) ”
  &&  “ (same_sign M_non_alias msize ) ”
  &&  “ ((Zabs (msize)) <= cap) ”
  &&  “ (msize = 1) ”
  &&  “ (1 <= M_non_alias) ”
  &&  “ (M_non_alias <= UINT_MAX) ”
  &&  (store_Z out_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (UIntArray.full ptr 1 (replace_Znth (0) (M_non_alias) ((cons (M_non_alias) ((@nil Z))))) )
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> msize)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((m_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.undef_seg ptr (Zabs (msize)) cap )
.

Definition combine_partial_solve_wit_11 :=
forall (B_non_alias: Z) (N_non_alias: Z) (A_non_alias: Z) (M_non_alias: Z) (out_pre: Z) (m_pre: Z) (a_pre: Z) (n_pre: Z) (b_pre: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (same_sign B_non_alias size )) (PreH3 : ((Zabs (size)) <= cap)),
  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (B_non_alias)) (Zabs (size)) )
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((b_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
  **  (store_Z n_pre N_non_alias )
|--
  “ (size <> 0) ”
  &&  “ (same_sign B_non_alias size ) ”
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (store_Z out_pre (M_non_alias * A_non_alias ) )
  **  (store_Z n_pre N_non_alias )
  **  (store_Z b_pre B_non_alias )
  **  (store_Z m_pre M_non_alias )
  **  (store_Z a_pre A_non_alias )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_combine_safety_wit_1 : combine_safety_wit_1.
Axiom proof_of_combine_safety_wit_2 : combine_safety_wit_2.
Axiom proof_of_combine_safety_wit_3 : combine_safety_wit_3.
Axiom proof_of_combine_safety_wit_4 : combine_safety_wit_4.
Axiom proof_of_combine_safety_wit_5 : combine_safety_wit_5.
Axiom proof_of_combine_safety_wit_6 : combine_safety_wit_6.
Axiom proof_of_combine_safety_wit_7 : combine_safety_wit_7.
Axiom proof_of_combine_safety_wit_8 : combine_safety_wit_8.
Axiom proof_of_combine_safety_wit_9 : combine_safety_wit_9.
Axiom proof_of_combine_safety_wit_10 : combine_safety_wit_10.
Axiom proof_of_combine_safety_wit_11 : combine_safety_wit_11.
Axiom proof_of_combine_entail_wit_1 : combine_entail_wit_1.
Axiom proof_of_combine_entail_wit_2_1 : combine_entail_wit_2_1.
Axiom proof_of_combine_entail_wit_2_2 : combine_entail_wit_2_2.
Axiom proof_of_combine_return_wit_1 : combine_return_wit_1.
Axiom proof_of_combine_return_wit_2 : combine_return_wit_2.
Axiom proof_of_combine_return_wit_3 : combine_return_wit_3.
Axiom proof_of_combine_return_wit_4 : combine_return_wit_4.
Axiom proof_of_combine_return_wit_5 : combine_return_wit_5.
Axiom proof_of_combine_return_wit_6 : combine_return_wit_6.
Axiom proof_of_combine_partial_solve_wit_1 : combine_partial_solve_wit_1.
Axiom proof_of_combine_partial_solve_wit_2 : combine_partial_solve_wit_2.
Axiom proof_of_combine_partial_solve_wit_3_pure : combine_partial_solve_wit_3_pure.
Axiom proof_of_combine_partial_solve_wit_3 : combine_partial_solve_wit_3.
Axiom proof_of_combine_partial_solve_wit_4 : combine_partial_solve_wit_4.
Axiom proof_of_combine_partial_solve_wit_5 : combine_partial_solve_wit_5.
Axiom proof_of_combine_partial_solve_wit_6 : combine_partial_solve_wit_6.
Axiom proof_of_combine_partial_solve_wit_7 : combine_partial_solve_wit_7.
Axiom proof_of_combine_partial_solve_wit_8 : combine_partial_solve_wit_8.
Axiom proof_of_combine_partial_solve_wit_9 : combine_partial_solve_wit_9.
Axiom proof_of_combine_partial_solve_wit_10 : combine_partial_solve_wit_10.
Axiom proof_of_combine_partial_solve_wit_11 : combine_partial_solve_wit_11.

End VC_Correct.
