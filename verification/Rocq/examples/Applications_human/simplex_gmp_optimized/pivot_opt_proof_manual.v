From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import pivot_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import pivot_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.pivot_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.normalize_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.violated_fme_model_selection_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib.
Local Open Scope sac.

Lemma proof_of_pivot_entail_wit_1 : pivot_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst r_pre e_pre.
  pose proof (simplex_dimensions_bounds _ _ PreH1) as (Hmatrix & _).
  replace (M_nonzero_pivot + (K_nonzero_pivot - M_nonzero_pivot))
    with K_nonzero_pivot in Hmatrix by lia.
  pose proof PreH1 as Hdimensions.
  destruct Hdimensions as (_ & Hnonbasic & Hcolumns & _).
  assert (Hr : 0 <= I_nonzero_pivot < M_nonzero_pivot) by lia.
  destruct (pivot_basis_distinct__pivot_result M_nonzero_pivot K_nonzero_pivot
    I_nonzero_pivot E_nonzero_pivot D_nonzero_pivot A_nonzero_pivot
    B_nonzero_pivot R_nonzero_pivot Hr ltac:(lia) ltac:(lia) PreH7 PreH9)
    as (Hleaving & Hdistinct & _).
  specialize (Hdistinct I_nonzero_pivot Hr).
  assert (Hrow : 0 <= I_nonzero_pivot * K_nonzero_pivot /\
    I_nonzero_pivot * K_nonzero_pivot + K_nonzero_pivot <=
      M_nonzero_pivot * K_nonzero_pivot) by nia.
  destruct Hrow as [Hrow0 Hrow_end].
  assert (Hoffset : unsigned_last_nbits (I_nonzero_pivot * K_nonzero_pivot) 32 =
    I_nonzero_pivot * K_nonzero_pivot).
  { apply unsigned_last_nbits_eq.
    assert (Hmax : INT_MAX < 2 ^ 32) by (vm_compute; reflexivity).
    lia. }
  rewrite Hoffset.
  replace (AP_nonzero_pivot + (I_nonzero_pivot * K_nonzero_pivot) *
      sizeof("__mpz_struct") + E_nonzero_pivot * sizeof("__mpz_struct"))
    with (AP_nonzero_pivot + (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot) *
      sizeof("__mpz_struct")) by ring.
  pose proof (MpzArray.full_split_to_missing_i AP_nonzero_pivot
    (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot)
    (M_nonzero_pivot * K_nonzero_pivot) A_nonzero_pivot 0 ltac:(lia)) as Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold mpz_store, mpz_sizeof.
  change (Znth (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot)
      A_nonzero_pivot 0)
    with (pivot_coef A_nonzero_pivot K_nonzero_pivot I_nonzero_pivot E_nonzero_pivot).
  unfold store_Z.
  Intros limbs size alloc.
  prop_apply (pivot_mpz_compact_sign limbs
    (pivot_coef A_nonzero_pivot K_nonzero_pivot I_nonzero_pivot E_nonzero_pivot)
    size ltac:(tauto)).
  Intros_p Hsize.
  destruct Hsize as [Hpositive Hzero].
  Exists limbs alloc size.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia | tauto].
Qed.

Lemma proof_of_pivot_entail_wit_2_1_split_goal_1 : pivot_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
  dump_pre_spatial.
  intros _.
  assert (Hnegative : PivotSize < 0) by lia.
  unfold same_sign in PreH3.
  lia.
Qed.

Lemma proof_of_pivot_entail_wit_2_1_split_goal_spatial : pivot_entail_wit_2_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH20, PreH26.
  pose proof (MpzArray.missing_i_merge_to_full AP_nonzero_pivot
    (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot)
    (M_nonzero_pivot * K_nonzero_pivot)
    (Znth (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot) A_nonzero_pivot 0)
    A_nonzero_pivot ltac:(lia)) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge.
  unfold mpz_store, mpz_sizeof in Hmerge.
  replace (AP_nonzero_pivot + (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot) *
      sizeof("__mpz_struct"))
    with (AP_nonzero_pivot + (I_nonzero_pivot * K_nonzero_pivot) *
      sizeof("__mpz_struct") + E_nonzero_pivot * sizeof("__mpz_struct"))
    in Hmerge by ring.
  fold (pivot_coef A_nonzero_pivot K_nonzero_pivot I_nonzero_pivot E_nonzero_pivot)
    in Hmerge.
  sep_apply_l_atomic Hmerge.
  sepcon_assoc_change. cancel.
Qed.

Lemma proof_of_pivot_entail_wit_2_1 : pivot_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pivot_entail_wit_2_1_split_goal_spatial.
  - Goal_apply proof_of_pivot_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_pivot_entail_wit_2_2_split_goal_spatial : pivot_entail_wit_2_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH20, PreH26.
  pose proof (MpzArray.missing_i_merge_to_full AP_nonzero_pivot
    (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot)
    (M_nonzero_pivot * K_nonzero_pivot)
    (Znth (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot) A_nonzero_pivot 0)
    A_nonzero_pivot ltac:(lia)) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge.
  unfold mpz_store, mpz_sizeof in Hmerge.
  replace (AP_nonzero_pivot + (I_nonzero_pivot * K_nonzero_pivot + E_nonzero_pivot) *
      sizeof("__mpz_struct"))
    with (AP_nonzero_pivot + (I_nonzero_pivot * K_nonzero_pivot) *
      sizeof("__mpz_struct") + E_nonzero_pivot * sizeof("__mpz_struct"))
    in Hmerge by ring.
  fold (pivot_coef A_nonzero_pivot K_nonzero_pivot I_nonzero_pivot E_nonzero_pivot)
    in Hmerge.
  sep_apply_l_atomic Hmerge.
  sepcon_assoc_change. cancel.
Qed.

Lemma proof_of_pivot_entail_wit_2_2 : pivot_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pivot_entail_wit_2_2_split_goal_spatial.
Qed.

Lemma proof_of_pivot_entail_wit_3_split_goal_spatial : pivot_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply_l_atomic (MpzArray.full_split_to_missing_i
    CP_nonzero_pivot I_nonzero_pivot M_nonzero_pivot C_nonzero_pivot 0 ltac:(lia)).
  unfold mpz_store, mpz_sizeof.
  cancel.
Qed.

Lemma proof_of_pivot_entail_wit_3 : pivot_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pivot_entail_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_pivot_entail_wit_4 : pivot_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia).
  rename C_nonzero_pivot into C, A_nonzero_pivot into A, CP_nonzero_pivot into CP,
    I_nonzero_pivot into I, M_nonzero_pivot into M, K_nonzero_pivot into K,
    AP_nonzero_pivot into AP.
  prop_apply_p (MpzArray.full_Zlength AP (M*K) A).
  Intros_p Hlength.
  Exists (-Znth I C 0) A.
  split_pure_spatial.
  - change (store_Z (CP + I * sizeof("__mpz_struct")) (-Znth I C 0))
      with (mpz_store CP I (-Znth I C 0)).
    sep_apply_l_atomic (MpzArray.missing_i_merge_to_full CP I M (-Znth I C 0) C ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    intros j v Hj Hv.
    change (sublist 0 0 N_nonzero_pivot) with (@nil Z).
    destruct (Z.eqb j I); [|reflexivity].
    destruct (in_dec Z.eq_dec v (@nil Z)) as [[] | _].
    reflexivity.
Qed.

Lemma proof_of_pivot_entail_wit_5_split_goal_1 : pivot_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  exact (proj2 (normalize_slot_range K_nonzero_pivot B_nonzero_pivot
    R_nonzero_pivot N_nonzero_pivot slot (proj1 PreH9) ltac:(lia))).
Qed.

Lemma proof_of_pivot_entail_wit_5_split_goal_2 : pivot_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  exact (proj2 (proj1 (normalize_slot_range K_nonzero_pivot B_nonzero_pivot
    R_nonzero_pivot N_nonzero_pivot slot (proj1 PreH9) ltac:(lia)))).
Qed.

Lemma proof_of_pivot_entail_wit_5_split_goal_3 : pivot_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  exact (proj1 (proj1 (normalize_slot_range K_nonzero_pivot B_nonzero_pivot
    R_nonzero_pivot N_nonzero_pivot slot (proj1 PreH9) ltac:(lia)))).
Qed.

Lemma proof_of_pivot_entail_wit_5 : pivot_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pivot_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_pivot_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_pivot_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_pivot_entail_wit_6 : pivot_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia).
  rename N_nonzero_pivot into N, A_nonzero_pivot into A, AP_nonzero_pivot into AP,
    I_nonzero_pivot into I, K_nonzero_pivot into K, M_nonzero_pivot into M.
  assert (Hfresh : ~ In v (sublist 0 slot N)).
  { rewrite PreH32.
    exact (proj1 (pivot_unvisited_nonbasic__pivot_negation N slot
      (proj1 (proj1 PreH9)) ltac:(lia))). }
  assert (Hcoef : Znth (I*K+v) Ac_2 0 = Znth (I*K+v) A 0).
  { specialize (PreH30 I v ltac:(lia) ltac:(lia)).
    rewrite Z.eqb_refl in PreH30.
    destruct (in_dec Z.eq_dec v (sublist 0 slot N)); [contradiction | exact PreH30]. }
  Exists T_2 Ac_2.
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i AP (I*K+v) (M*K) Ac_2 0 ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    rewrite Hcoef, PreH20.
    replace (AP + I*K*sizeof("__mpz_struct") + v*sizeof("__mpz_struct"))
      with (AP + (I*K+v)*sizeof("__mpz_struct")) by ring.
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_pivot_entail_wit_7 : pivot_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia).
  rename N_nonzero_pivot into N, A_nonzero_pivot into A, AP_nonzero_pivot into AP,
    I_nonzero_pivot into I, K_nonzero_pivot into K, M_nonzero_pivot into M.
  subst v.
  set (v := Znth slot N 0) in *.
  set (p := I*K+v) in *.
  set (negated := -Znth p A 0) in *.
  change (MpzArray.missing_i AP p 0 (M*K) Ac_2)
    with (store_array_missing_i_rec mpz_store AP p 0 (M*K) Ac_2).
  prop_apply_p (@store_array_missing_i_rec_Zlength Z mpz_store AP p 0 (M*K) Ac_2).
  change (store_array_missing_i_rec mpz_store AP p 0 (M*K) Ac_2)
    with (MpzArray.missing_i AP p 0 (M*K) Ac_2).
  Intros_p Hlength.
  Exists negated (replace_Znth p negated Ac_2).
  split_pure_spatial.
  - rewrite PreH19.
    replace (AP + I*K*sizeof("__mpz_struct") + v*sizeof("__mpz_struct"))
      with (AP + p*sizeof("__mpz_struct")) by (unfold p; ring).
    change (store_Z (AP + p*sizeof("__mpz_struct")) negated) with (mpz_store AP p negated).
    sep_apply_l_atomic (MpzArray.missing_i_merge_to_full AP p (M*K) negated Ac_2 ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold negated, p, v.
    apply pivot_negated_slots_step__pivot_negation;
      first [exact (proj1 (proj1 PreH8)) | assumption | lia].
Qed.

Lemma proof_of_pivot_entail_wit_8 : pivot_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  rename D_nonzero_pivot into D, DP_nonzero_pivot into DP, AP_nonzero_pivot into AP,
    I_nonzero_pivot into I, K_nonzero_pivot into K, M_nonzero_pivot into M.
  replace slot with (K-M) in PreH30 by lia.
  Exists T_2 Ac_2.
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i DP I M D 0 ltac:(lia)).
    sep_apply_l_atomic (MpzArray.full_split_to_missing_i AP (I*K+b) (M*K) Ac_2 0 ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    rewrite PreH20.
    replace (AP + I*K*sizeof("__mpz_struct") + b*sizeof("__mpz_struct"))
      with (AP + (I*K+b)*sizeof("__mpz_struct")) by ring.
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_pivot_entail_wit_9_split_goal_1 : pivot_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (MpzArray.full_Zlength AP_nonzero_pivot
    (M_nonzero_pivot * K_nonzero_pivot) A_nonzero_pivot).
  Intros_p Hlength.
  dump_pre_spatial. exact Hlength.
Qed.

Lemma proof_of_pivot_entail_wit_9_split_goal_spatial : pivot_entail_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_nonzero_pivot into A,
    D_nonzero_pivot into D,
    AP_nonzero_pivot into ap,
    DP_nonzero_pivot into dp,
    I_nonzero_pivot into i,
    K_nonzero_pivot into k,
    M_nonzero_pivot into m.
  replace (a + b * sizeof ("__mpz_struct")) with
    (ap + (i*k+b) * sizeof ("__mpz_struct")) by (rewrite PreH19; ring).
  sep_apply_l_atomic (MpzArray.full_split_to_missing_i dp i m D 0 ltac:(lia)).
  sep_apply_l_atomic (MpzArray.full_split_to_missing_i ap (i*k+b) (m*k) A 0 ltac:(lia)).
  unfold mpz_store, mpz_sizeof.
  cancel.
Qed.

Lemma proof_of_pivot_entail_wit_9 : pivot_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pivot_entail_wit_9_split_goal_spatial.
  - Goal_apply proof_of_pivot_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_pivot_entail_wit_10_1 : pivot_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_nonzero_pivot into A,
    C_nonzero_pivot into C,
    D_nonzero_pivot into D,
    AP_nonzero_pivot into ap,
    E_nonzero_pivot into e,
    I_nonzero_pivot into i,
    K_nonzero_pivot into k,
    M_nonzero_pivot into m.
  replace (a + b * sizeof ("__mpz_struct")) with
    (ap + (i*k+b) * sizeof ("__mpz_struct")) by (rewrite PreH19; ring).
  pose proof (MpzArray.missing_i_merge_to_full ap (i*k+b) (m*k)
    (Znth i D 0) Ac ltac:(lia)) as Hmerge.
  unfold mpz_store, mpz_sizeof in Hmerge.
  sep_apply_l_atomic Hmerge.
  prop_apply_p (MpzArray.full_Zlength ap (m*k)
    (replace_Znth (i*k+b) (Znth i D 0) Ac)).
  Intros_p Hlength.
  rewrite Zlength_replace_Znth in Hlength.
  Exists T_2 (replace_Znth i (- Znth i C 0) C)
    (replace_Znth (i*k+b) (Znth i D 0) Ac).
  replace (a + e * sizeof ("__mpz_struct")) with
    (ap + (i*k+e) * sizeof ("__mpz_struct")) by (rewrite PreH19; ring).
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i ap (i*k+e) (m*k)
      (replace_Znth (i*k+b) (Znth i D 0) Ac) 0 ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply pivot_raw_positive__raw_pivot_row; eauto; lia.
Qed.

Lemma proof_of_pivot_entail_wit_10_2 : pivot_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_nonzero_pivot into A,
    C_nonzero_pivot into C,
    D_nonzero_pivot into D,
    AP_nonzero_pivot into ap,
    E_nonzero_pivot into e,
    I_nonzero_pivot into i,
    K_nonzero_pivot into k,
    M_nonzero_pivot into m.
  replace (a + b * sizeof ("__mpz_struct")) with
    (ap + (i*k+b) * sizeof ("__mpz_struct")) by (rewrite PreH19; ring).
  pose proof (MpzArray.missing_i_merge_to_full ap (i*k+b) (m*k)
    (- Znth i D 0) A ltac:(lia)) as Hmerge.
  unfold mpz_store, mpz_sizeof in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists (- Znth i D 0) C (replace_Znth (i*k+b) (- Znth i D 0) A).
  replace (a + e * sizeof ("__mpz_struct")) with
    (ap + (i*k+e) * sizeof ("__mpz_struct")) by (rewrite PreH19; ring).
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i ap (i*k+e) (m*k)
      (replace_Znth (i*k+b) (- Znth i D 0) A) 0 ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    eapply pivot_raw_negative__raw_pivot_row; eauto; lia.
Qed.

Lemma proof_of_pivot_entail_wit_11 : pivot_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_nonzero_pivot into A,
    D_nonzero_pivot into D,
    AP_nonzero_pivot into ap,
    DP_nonzero_pivot into dp,
    E_nonzero_pivot into e,
    I_nonzero_pivot into i,
    K_nonzero_pivot into k,
    M_nonzero_pivot into m.
  rewrite PreH13.
  replace (a + e * sizeof ("__mpz_struct")) with
    (ap + (i*k+e) * sizeof ("__mpz_struct")) by (rewrite PreH19; ring).
  pose proof (MpzArray.missing_i_merge_to_full dp i m
    (Z.abs (pivot_coef A k i e)) D ltac:(lia)) as HmergeD.
  pose proof (MpzArray.missing_i_merge_to_full ap (i*k+e) (m*k)
    0 A0 ltac:(lia)) as HmergeA.
  unfold mpz_store, mpz_sizeof in HmergeD, HmergeA.
  sep_apply_l_atomic HmergeD.
  prop_apply_p (@store_array_missing_i_rec_Zlength Z mpz_store ap (i*k+e) 0 (m*k) A0).
  Intros_p Hlength.
  change (store_array_missing_i_rec mpz_store ap (i*k+e) 0 (m*k) A0)
    with (MpzArray.missing_i ap (i*k+e) 0 (m*k) A0).
  sep_apply_l_atomic HmergeA.
  Exists T_2 (replace_Znth i (Z.abs (pivot_coef A k i e)) D)
    C0 (replace_Znth (i*k+e) 0 A0).
  split_pure_spatial.
  - sepcon_right_assoc.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_pivot_entail_wit_12_split_goal_1 : pivot_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [[Hnd _] _].
  assert (slot = Q_nonzero_pivot).
  { apply (proj1 (pivot_nodup_indices__basis_metadata N_nonzero_pivot) Hnd);
      [lia | lia | congruence]. }
  now subst slot.
Qed.

Lemma proof_of_pivot_entail_wit_12 : pivot_entail_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pivot_entail_wit_12_split_goal_1.
Qed.

Lemma proof_of_pivot_entail_wit_13_split_goal_1 : pivot_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (slot <> Q_nonzero_pivot) by congruence.
  lia.
Qed.

Lemma proof_of_pivot_entail_wit_13 : pivot_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pivot_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_pivot_entail_wit_14_split_goal_1 : pivot_entail_wit_14_split_goal_1.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14_split_goal_2 : pivot_entail_wit_14_split_goal_2.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14_split_goal_3 : pivot_entail_wit_14_split_goal_3.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14_split_goal_4 : pivot_entail_wit_14_split_goal_4.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14_split_goal_5 : pivot_entail_wit_14_split_goal_5.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14_split_goal_6 : pivot_entail_wit_14_split_goal_6.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14_split_goal_7 : pivot_entail_wit_14_split_goal_7.
Proof. Abort.

Lemma proof_of_pivot_entail_wit_14 : pivot_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst b Nn_2.
  prop_apply_p (UIntArray.full_Zlength BP_nonzero_pivot M_nonzero_pivot
    (pivot_basic I_nonzero_pivot E_nonzero_pivot B_nonzero_pivot)).
  Intros_p Hbasic_length.
  prop_apply_p (UIntArray.full_Zlength RP_nonzero_pivot K_nonzero_pivot
    (pivot_row_map I_nonzero_pivot E_nonzero_pivot B_nonzero_pivot R_nonzero_pivot)).
  Intros_p Hrow_length.
  prop_apply_p (MpzArray.full_Zlength DP_nonzero_pivot M_nonzero_pivot Dr_2).
  Intros_p Hden_length.
  unfold pivot_basic in Hbasic_length.
  unfold pivot_row_map in Hrow_length.
  rewrite Zlength_replace_Znth in Hbasic_length.
  rewrite !Zlength_replace_Znth in Hrow_length.
  pose proof (pivot_swap_nonbasic__basis_metadata
    M_nonzero_pivot K_nonzero_pivot I_nonzero_pivot E_nonzero_pivot Q_nonzero_pivot
    D_nonzero_pivot A_nonzero_pivot B_nonzero_pivot R_nonzero_pivot N_nonzero_pivot
    ltac:(lia) ltac:(lia) ltac:(lia) PreH21 Hbasic_length Hrow_length
    PreH7 PreH8 ltac:(lia) PreH13 PreH9) as Hnonbasic.
  pose proof (proj1 Hnonbasic) as Hcolumns.
  pose proof PreH26 as [Hrawden [_ Hrawcoef]].
  assert (Hpositive : 0 < Znth I_nonzero_pivot Dr_2 0).
  { rewrite Hrawden in Hden_length |- *.
    rewrite Zlength_replace_Znth in Hden_length.
    rewrite Znth_replace_Znth_Same by lia.
    apply Z.abs_pos. exact PreH10. }
  assert (Hzero : normalize_basic_zero K_nonzero_pivot I_nonzero_pivot Ar_2
      (pivot_basic I_nonzero_pivot E_nonzero_pivot B_nonzero_pivot)).
  { destruct (pivot_basis_distinct__pivot_result M_nonzero_pivot K_nonzero_pivot
      I_nonzero_pivot E_nonzero_pivot D_nonzero_pivot A_nonzero_pivot
      B_nonzero_pivot R_nonzero_pivot ltac:(lia) ltac:(lia) PreH21
      PreH7 PreH9) as [_ [Hnotenter Hdistinct]].
    destruct PreH7 as [Hentry [_ Hentryzero]].
    unfold normalize_basic_zero. apply Forall_forall. intros v Hv.
    apply pivot_member_at__basis_metadata in Hv. destruct Hv as [j [Hj <-]].
    unfold pivot_basic in *.
    rewrite Zlength_replace_Znth in Hj. rewrite Hbasic_length in Hj.
    change (pivot_coef Ar_2 K_nonzero_pivot I_nonzero_pivot
      (Znth j (replace_Znth I_nonzero_pivot E_nonzero_pivot B_nonzero_pivot) 0) = 0).
    destruct (Z.eq_dec I_nonzero_pivot j) as [<- | Hother].
    - rewrite Znth_replace_Znth_Same by lia.
      rewrite Hrawcoef by lia. rewrite Z.eqb_refl.
      unfold pivot_row_coef. now rewrite Z.eqb_refl.
    - rewrite Znth_replace_Znth_Diff by lia.
      destruct (Hentry j Hj) as [Hcolumn _].
      rewrite Hrawcoef by lia. rewrite Z.eqb_refl.
      unfold pivot_row_coef.
      rewrite (proj2 (Z.eqb_neq _ _) (Hnotenter j Hj)).
      rewrite (proj2 (Z.eqb_neq _ _) (Hdistinct j Hj ltac:(lia))).
      unfold pivot_coef. rewrite Hentryzero by lia. ring. }
  Exists T_2 (replace_Znth Q_nonzero_pivot (Znth I_nonzero_pivot B_nonzero_pivot 0)
    N_nonzero_pivot)
    (pivot_row_map I_nonzero_pivot E_nonzero_pivot B_nonzero_pivot R_nonzero_pivot)
    (pivot_basic I_nonzero_pivot E_nonzero_pivot B_nonzero_pivot) Dr_2 Cr_2 Ar_2.
  split_pure_spatial.
  - unfold pivot_basic, pivot_row_map. sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial.
    all: first [assumption | reflexivity | (rewrite Zlength_replace_Znth; assumption)
      | (split; assumption)].
Qed.

Lemma proof_of_pivot_entail_wit_15 : pivot_entail_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K.
  rename I_nonzero_pivot into I, E_nonzero_pivot into E.
  rename DP_nonzero_pivot into DP, CP_nonzero_pivot into CP.
  rename D_nonzero_pivot into D, C_nonzero_pivot into C.
  rename A_nonzero_pivot into A, B_nonzero_pivot into B.
  rename PreH1 into Hnormalize, PreH27 into Hraw.
  rename PreH28 into HAr, PreH35 into Hraw_positive, PreH37 into HA.
  prop_apply_p (MpzArray.full_Zlength DP M Dn). Intros_p HDn.
  prop_apply_p (MpzArray.full_Zlength CP M Cn). Intros_p HCn.
  pose proof Hnormalize as (HDn_replace & HCn_replace & _).
  rewrite HDn_replace, Zlength_replace_Znth in HDn.
  rewrite HCn_replace, Zlength_replace_Znth in HCn.
  pose proof Hraw as (HDr_replace & HCr_replace & _).
  assert (HD : Zlength D = M).
  { rewrite HDr_replace, Zlength_replace_Znth in HDn. exact HDn. }
  assert (HC : Zlength C = M).
  { rewrite HCr_replace, Zlength_replace_Znth in HCn. exact HCn. }
  assert (Hcols : forall v, In v Nn_2 -> 0 <= v < K).
  { destruct PreH34 as (_ & _ & Hnb & _).
    intros v Hv. exact (proj1 (Hnb v Hv)). }
  destruct (pivot_normalized_prefix_initial__first_normalization M K I E
    D C A B Nn_2 Dr Cr Ar Dn Cn An ltac:(lia) ltac:(lia)
    HD HC HDn HCn HA HAr Hcols Hraw Hnormalize Hraw_positive)
    as [Hprefix Hpositive].
  Exists T_2 Dn Cn An Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i DP I M Dn 0 ltac:(lia)).
    change (mpz_store DP I (Znth I Dn 0))
      with (store_Z (DP + I * sizeof ("__mpz_struct")) (Znth I Dn 0)).
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_pivot_entail_wit_16 : pivot_entail_wit_16.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, I_nonzero_pivot into I, DP_nonzero_pivot into DP.
  Exists T_2 0 0 0 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - change (store_Z (DP + I * sizeof ("__mpz_struct")) (Znth I Db_2 0))
      with (mpz_store DP I (Znth I Db_2 0)).
    sep_apply_l_atomic (MpzArray.missing_i_merge_to_full DP I M
      (Znth I Db_2 0) Db_2 ltac:(lia)).
    rewrite replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_pivot_entail_wit_17 : pivot_entail_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename AP_nonzero_pivot into AP, M_nonzero_pivot into M,
    K_nonzero_pivot into K, I_nonzero_pivot into I, E_nonzero_pivot into E,
    D_nonzero_pivot into D, C_nonzero_pivot into C, A_nonzero_pivot into A.
  assert (Hrow_bound : i * K + K <= M * K).
  { replace (i * K + K) with ((i + 1) * K) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (Hproduct : 0 <= i * K) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hindex : 0 <= i * K + E < M * K) by lia.
  assert (Hunsigned : unsigned_last_nbits (i * K) 32 = i * K).
  { apply unsigned_last_nbits_eq.
    change (0 <= i * K < 4294967296).
    change (M * K <= 2147483647) in PreH25.
    nia. }
  pose proof (PreH34 i ltac:(lia)) as Hrow.
  rewrite (proj2 (Z.eqb_neq i I) PreH1), Z.ltb_irrefl in Hrow.
  change (pivot_row_snapshot K i Db_2 Cb_2 Ab_2 =
    pivot_row_snapshot K i D C A) in Hrow.
  pose proof (f_equal (@snd (Z * Z) (list Z)) Hrow) as Hslice.
  change (sublist (i * K) ((i + 1) * K) Ab_2 =
    sublist (i * K) ((i + 1) * K) A) in Hslice.
  apply (f_equal (fun row => Znth E row 0)) in Hslice.
  rewrite !pivot_row_slice_coef in Hslice by lia.
  change (Znth (i * K + E) Ab_2 0 = pivot_coef A K i E) in Hslice.
  pose proof (MpzArray.full_split_to_missing_i AP (i * K + E)
    (M * K) Ab_2 0 Hindex) as Hsplit.
  rewrite Hslice in Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  let cell := constr:(store_Z (AP + (i * K + E) * sizeof ("__mpz_struct"))
    (pivot_coef A K i E)) in
  let opened := eval unfold store_Z in cell in change cell with opened.
  Intros limbs size capacity.
  assert (Hsame : same_sign (pivot_coef A K i E) size) by assumption.
  prop_apply_p (pivot_mpz_compact_sign limbs (pivot_coef A K i E) size Hsame).
  Intros_p Hsign.
  destruct Hsign as [_ [Hsize_zero Hvalue_zero]].
  Exists T_2 Nu_2 Mu_2 G_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2 limbs capacity size.
  rewrite Hunsigned.
  split_pure_spatial.
  - replace (AP + i * K * sizeof ("__mpz_struct") + E * sizeof ("__mpz_struct"))
      with (AP + (i * K + E) * sizeof ("__mpz_struct")) by ring.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia | nia].
Qed.

Lemma proof_of_pivot_entail_wit_18 : pivot_entail_wit_18.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename I_nonzero_pivot into I, E_nonzero_pivot into E,
    K_nonzero_pivot into K, A_nonzero_pivot into A.
  assert (Hx : pivot_coef A K i E <> 0) by (intro Hz; apply PreH1, PreH5, Hz).
  destruct (pivot_gcd_exact (Znth I Db_2 0) (pivot_coef A K i E) PreH40)
    as [Hg [Hdivide_p Hdivide_x]].
  rewrite PreH18.
  Exists T_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | apply addr_of_LE_var_not_zero].
Qed.

Lemma proof_of_pivot_entail_wit_19 : pivot_entail_wit_19.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH32 i ltac:(lia)) as Hrow.
  rewrite (proj2 (Z.eqb_neq i I_nonzero_pivot) PreH37), Z.ltb_irrefl in Hrow.
  cbn in Hrow.
  unfold pivot_row_snapshot in Hrow.
  assert (Hd : Znth i Db_2 0 = Znth i D_nonzero_pivot 0) by congruence.
  pose proof (f_equal (fun row : Z * Z * list Z => Znth E_nonzero_pivot (snd row) 0) Hrow) as Hcoef.
  change (Znth E_nonzero_pivot (sublist (i*K_nonzero_pivot) ((i+1)*K_nonzero_pivot) Ab_2) 0 =
          Znth E_nonzero_pivot (sublist (i*K_nonzero_pivot) ((i+1)*K_nonzero_pivot) A_nonzero_pivot) 0)
    in Hcoef.
  rewrite !pivot_row_slice_coef in Hcoef by lia.
  unfold pivot_coef at 1 in Hcoef.
  rewrite PreH13, PreH38.
  replace (AP_nonzero_pivot + i * K_nonzero_pivot * sizeof("__mpz_struct") +
    E_nonzero_pivot * sizeof("__mpz_struct"))
    with (AP_nonzero_pivot + (i * K_nonzero_pivot + E_nonzero_pivot) * sizeof("__mpz_struct"))
    by ring.
  pose proof (MpzArray.missing_i_merge_to_full AP_nonzero_pivot
     (i * K_nonzero_pivot + E_nonzero_pivot) (M_nonzero_pivot * K_nonzero_pivot)
     (Znth (i * K_nonzero_pivot + E_nonzero_pivot) Ab_2 0) Ab_2 ltac:(lia)) as Hmerge.
  rewrite Hcoef in Hmerge at 1.
  unfold mpz_store, mpz_sizeof in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite replace_Znth_Znth.
  pose proof (MpzArray.full_split_to_missing_i DP_nonzero_pivot i M_nonzero_pivot Db_2 0 ltac:(lia)) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  rewrite Hd.
  set (x := pivot_coef A_nonzero_pivot K_nonzero_pivot i E_nonzero_pivot) in *.
  set (d := Znth I_nonzero_pivot Db_2 0) in *.
  set (mu := Z.quot d (Z.gcd d x)) in *.
  set (nu := Z.quot x (Z.gcd d x)) in *.
  assert (Hmu : 0 < mu) by (unfold pivot_divides_exactly in PreH45; fold mu in PreH45; nia).
  unfold store_Z at 4.
  Intros md ms mc.
  destruct (Z.eq_dec ms 1) as [-> | Hsize].
  - rewrite (Z.abs_eq mu) by lia.
    change (Z.abs 1) with 1.
    sep_apply_l_atomic (normalize_single_limb_open md mu).
    Intros_p Hlimb.
    Left.
    Exists T_2 md mc 1 nu mu Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
    rewrite ?eval_addr.
    unfold mu, nu, d, x.
    change (Zabs 1) with 1 in *.
    split_pure_spatial.
    + sepcon_assoc_change. cancel.
    + split_pures; dump_pre_spatial;
        try fold x; try fold d; try fold mu; try fold nu;
        first [assumption | reflexivity | unfold UINT_MOD in Hlimb; lia].
  - Right.
    Exists T_2 md mc ms nu mu Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
    rewrite ?eval_addr.
    unfold mu, nu, d, x.
    change (Zabs 1) with 1 in *.
    split_pure_spatial.
    + sepcon_assoc_change. cancel.
    + split_pures; dump_pre_spatial;
        try fold x; try fold d; try fold mu; try fold nu;
        first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_pivot_entail_wit_20_1 : pivot_entail_wit_20_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (store_Z_from_fields (&("m")) md ms mc Mu_2 ltac:(assumption) ltac:(assumption)) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "m")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  Exists T_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_pivot_entail_wit_20_2 : pivot_entail_wit_20_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (replace_Znth 0 Mu_2 (Mu_2 :: nil)) with (Mu_2 :: nil) by reflexivity.
  assert (Hlimb : 1 <= Mu_2 < UINT_MOD) by (unfold UINT_MOD in *; lia).
  pose proof (normalize_single_limb_close md Mu_2 Hlimb) as Hcompact.
  replace (mpd_store_Z_compact UINT_MOD md Mu_2 1)
    with (mpd_store_Z_compact UINT_MOD md (Zabs Mu_2) (Zabs ms)) in Hcompact
    by (rewrite (Z.abs_eq Mu_2) by lia; replace ms with 1 by lia; reflexivity).
  sep_apply_l_atomic Hcompact.
  pose proof (store_Z_from_fields (&("m")) md ms mc Mu_2 ltac:(assumption) ltac:(assumption)) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "m")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  Exists T_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_pivot_entail_wit_21_1 : pivot_entail_wit_21_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (replace_Znth 0 Mu_2 (Mu_2 :: nil)) with (Mu_2 :: nil) by reflexivity.
  assert (Hlimb : 1 <= Mu_2 < UINT_MOD) by (unfold UINT_MOD in *; lia).
  pose proof (normalize_single_limb_close md Mu_2 Hlimb) as Hcompact.
  replace (mpd_store_Z_compact UINT_MOD md Mu_2 1)
    with (mpd_store_Z_compact UINT_MOD md (Zabs Mu_2) (Zabs ms)) in Hcompact
    by (rewrite (Z.abs_eq Mu_2) by lia; replace ms with 1 by lia; reflexivity).
  sep_apply_l_atomic Hcompact.
  pose proof (store_Z_from_fields (&("m")) md ms mc Mu_2 ltac:(assumption) ltac:(assumption)) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "m")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  pose proof (MpzArray.missing_i_merge_to_full DP_nonzero_pivot i M_nonzero_pivot
    (Mu_2 * Znth i D_nonzero_pivot 0) Db_2 ltac:(lia)) as Hmerge.
  unfold mpz_store, mpz_sizeof in Hmerge.
  replace (Mu_2 * Znth i D_nonzero_pivot 0) with (Znth i D_nonzero_pivot 0) in Hmerge at 1
    by (rewrite PreH1; lia).
  sep_apply_l_atomic Hmerge.
  match goal with Hp : pivot_normalized_prefix _ _ _ _ i _ _ _ _ _ _ _ _ |- _ =>
    pose proof (Hp i ltac:(lia)) as Hrow
  end.
  rewrite (proj2 (Z.eqb_neq i I_nonzero_pivot) ltac:(lia)), Z.ltb_irrefl in Hrow.
  cbn in Hrow.
  unfold pivot_row_snapshot in Hrow.
  assert (Hc : Znth i Cb_2 0 = Znth i C_nonzero_pivot 0) by congruence.
  prop_apply_p (MpzArray.full_Zlength CP_nonzero_pivot M_nonzero_pivot Cb_2).
  Intros_p Hlen.
  pose proof (pivot_open_two__eliminate_two_cells CP_nonzero_pivot M_nonzero_pivot
    i I_nonzero_pivot Cb_2 ltac:(lia) ltac:(lia) ltac:(lia) Hlen) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  rewrite Hc in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  rewrite PreH1, Z.mul_1_l.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_pivot_entail_wit_21_2 : pivot_entail_wit_21_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH13, <- PreH44.
  pose proof (MpzArray.missing_i_merge_to_full DP_nonzero_pivot i M_nonzero_pivot
    (Mu_2 * Znth i D_nonzero_pivot 0) Db_2 ltac:(lia)) as Hmerge.
  unfold mpz_store, mpz_sizeof in Hmerge.
  sep_apply_l_atomic Hmerge.
  match goal with Hp : pivot_normalized_prefix _ _ _ _ i _ _ _ _ _ _ _ _ |- _ =>
    pose proof (Hp i ltac:(lia)) as Hrow
  end.
  rewrite (proj2 (Z.eqb_neq i I_nonzero_pivot) ltac:(lia)), Z.ltb_irrefl in Hrow.
  cbn in Hrow.
  unfold pivot_row_snapshot in Hrow.
  assert (Hc : Znth i Cb_2 0 = Znth i C_nonzero_pivot 0) by congruence.
  prop_apply_p (MpzArray.full_Zlength CP_nonzero_pivot M_nonzero_pivot Cb_2).
  Intros_p Hlen.
  pose proof (pivot_open_two__eliminate_two_cells CP_nonzero_pivot M_nonzero_pivot
    i I_nonzero_pivot Cb_2 ltac:(lia) ltac:(lia) ltac:(lia) Hlen) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  rewrite Hc in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_pivot_entail_wit_22 : pivot_entail_wit_22.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K,
    I_nonzero_pivot into I, E_nonzero_pivot into E, A_nonzero_pivot into A.
  rename C_nonzero_pivot into C, CP_nonzero_pivot into CP.
  prop_apply_p (MpzArray.full_Zlength AP_nonzero_pivot (M*K) Ab_2).
  Intros_p Hab_length.
  assert (Hi : 0 <= i < M) by lia.
  assert (HI : 0 <= I < M) by lia.
  prop_apply_p (pivot_two_cells_lengths__eliminate_two_cells CP M i I Cb_2).
  Intros_p Hlengths.
  destruct Hlengths as [Hfirst [Hmiddle Hlast]].
  set (rebuild := fun x y =>
    (sublist 0 (Z.min i I) Cb_2 ++ (if Z.ltb i I then x else y) ::
     sublist (Z.min i I + 1) (Z.max i I) Cb_2 ++
       (if Z.ltb i I then y else x) :: sublist (Z.max i I + 1) M Cb_2)%list).
  set (Cb' := rebuild (Znth i Cb_2 0) (Znth I Cb_2 0)).
  set (T := Mu_2 * Znth i C 0 + Nu_2 * Znth I Cb_2 0).
  destruct (pivot_two_cells_replace__eliminate_two_cells M i I Cb_2 T
    Hi HI PreH37 Hfirst Hmiddle Hlast) as [Hbase Hreplace].
  change (forall j, 0 <= j < M -> Znth j Cb' 0 = Znth j Cb_2 0) in Hbase.
  change (rebuild T (Znth I Cb_2 0) = replace_Znth i T Cb') in Hreplace.
  assert (Hprefix : pivot_normalized_prefix M K I E i D_nonzero_pivot C A
      B_nonzero_pivot Nn_2 Db_2 Cb' Ab_2).
  { intros j Hj. unfold pivot_row_snapshot at 1. rewrite Hbase by lia.
    apply PreH32, Hj. }
  rewrite PreH13, <- PreH44, <- PreH45.
  fold T.
  Exists T Ab_2 Nu_2 Mu_2 Db_2 Cb' Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - rewrite Hbase by lia. fold T. rewrite <- Hreplace.
    pose proof (pivot_merge_two_update__eliminate_two_cells CP M i I Cb_2
      T (Znth I Cb_2 0) Hi HI PreH37 Hfirst Hmiddle) as Hmerge.
    unfold mpz_store, mpz_sizeof in Hmerge.
    sep_apply_l_atomic Hmerge.
    sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial;
      try (first [assumption | reflexivity | congruence | lia]).
    unfold pivot_elimination_slots.
    intros j v Hj Hv.
    replace (sublist 0 0 Nn_2) with (@nil Z) by reflexivity.
    now destruct (Z.eqb j i), (Z.eqb v E).
Qed.

Lemma proof_of_pivot_entail_wit_23 : pivot_entail_wit_23.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (normalize_slot_range K_nonzero_pivot Bn_2 Rn_2 Nn slot
    PreH32 ltac:(lia)) as [[Hlo Hhi] Hmap].
  Exists T_2 Ac_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | congruence | lia].
Qed.

Lemma proof_of_pivot_entail_wit_24 : pivot_entail_wit_24.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K,
    I_nonzero_pivot into I, E_nonzero_pivot into E, A_nonzero_pivot into A.
  rename AP_nonzero_pivot into AP.
  assert (Hi : 0 <= i < M) by lia.
  assert (HI : 0 <= I < M) by lia.
  assert (Hv : 0 <= v < K) by lia.
  assert (Hslot : 0 <= slot < Zlength Nn_2) by lia.
  pose proof (pivot_slot_absent__elimination_columns Nn_2 slot
    (proj1 PreH33) Hslot) as Habsent.
  rewrite <- PreH53 in Habsent.
  pose proof (PreH51 i v Hi Hv) as Hactive.
  rewrite Z.eqb_refl, (proj2 (Z.eqb_neq v E) PreH2) in Hactive.
  cbn [andb negb] in Hactive.
  destruct (in_dec Z.eq_dec v (sublist 0 slot Nn_2)); [contradiction|].
  pose proof (PreH34 i Hi) as Hrow.
  rewrite (proj2 (Z.eqb_neq i I) PreH39), Z.ltb_irrefl in Hrow.
  pose proof (f_equal (fun row => Znth v (snd row) 0) Hrow) as Horiginal.
  cbn [orb pivot_row_snapshot snd] in Horiginal.
  repeat rewrite pivot_row_slice_coef in Horiginal by lia.
  rewrite Horiginal in Hactive.
  pose proof (PreH51 I v HI Hv) as Hpivot.
  rewrite (proj2 (Z.eqb_neq I i) ltac:(lia)) in Hpivot.
  cbn in Hpivot.
  unfold pivot_coef in Hactive, Hpivot.
  assert (Hix : 0 <= i*K+v < M*K) by lia.
  assert (HIx : 0 <= I*K+v < M*K) by lia.
  assert (Hdifferent : i*K+v <> I*K+v).
  { intro Heq.
    destruct (pivot_flat_same_cell__eliminate_two_cells K i I v v
      ltac:(lia) Hv Hv Heq). contradiction. }
  prop_apply_p (MpzArray.full_Zlength AP (M*K) Ac_2).
  Intros_p Hlength.
  Exists T_2 Ac_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - pose proof (pivot_open_two__eliminate_two_cells AP (M*K) (i*K+v) (I*K+v) Ac_2
      Hix HIx Hdifferent Hlength) as Hsplit.
    unfold mpz_store, mpz_sizeof in Hsplit.
    rewrite Hactive, Hpivot in Hsplit.
    sep_apply_l_atomic Hsplit.
    rewrite PreH40, PreH21.
    replace (AP + i*K*sizeof("__mpz_struct") + v*sizeof("__mpz_struct"))
      with (AP + (i*K+v)*sizeof("__mpz_struct")) by ring.
    replace (AP + I*K*sizeof("__mpz_struct") + v*sizeof("__mpz_struct"))
      with (AP + (I*K+v)*sizeof("__mpz_struct")) by ring.
    sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia | congruence].
Qed.

Lemma proof_of_pivot_entail_wit_25_1 : pivot_entail_wit_25_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K,
    I_nonzero_pivot into I, E_nonzero_pivot into E, A_nonzero_pivot into A.
  rename AP_nonzero_pivot into AP.
  assert (Hslot : 0 <= slot < Zlength Nn_2) by lia.
  assert (Hv : 0 <= v < K) by lia.
  set (left := i*K+v).
  set (right := I*K+v).
  assert (Hleft : 0 <= left < M*K) by (unfold left; lia).
  assert (Hright : 0 <= right < M*K) by (unfold right; lia).
  assert (Hdifferent : left <> right) by (unfold left, right; assumption).
  prop_apply_p (pivot_two_cells_lengths__eliminate_two_cells AP (M*K) left right Ac_2).
  Intros_p Hlengths.
  destruct Hlengths as [Hfirst [Hmiddle _]].
  set (T := Mu_2 * Znth left A 0 + Nu_2 * Znth right Ab_2 0).
  set (Ac' := (sublist 0 (Z.min left right) Ac_2 ++
    (if Z.ltb left right then T else Znth right Ab_2 0) ::
    sublist (Z.min left right + 1) (Z.max left right) Ac_2 ++
    (if Z.ltb left right then Znth right Ab_2 0 else T) ::
    sublist (Z.max left right + 1) (M*K) Ac_2)%list).
  assert (Hstep : pivot_elimination_slots M K I E i (slot+1) Mu_2 Nu_2 A Nn_2 Ab_2 Ac').
  { eapply pivot_elimination_slot_step__elimination_columns; [exact Hslot|exact PreH49|].
    intros j u Hj Hu.
    rewrite <- PreH51.
    unfold pivot_coef at 1.
    unfold Ac'.
    assert (Hindex : 0 <= j*K+u < M*K).
    { assert (Hrow_end : (j+1)*K <= M*K) by
        (apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hrow_begin : 0 <= j*K) by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
    rewrite (pivot_two_cells_value__eliminate_two_cells (M*K) left right Ac_2
      T (Znth right Ab_2 0) (j*K+u) Hleft Hright Hdifferent Hindex Hfirst Hmiddle).
    destruct (Z.eq_dec (j*K+u) left) as [Hsame|Hother].
    - apply (pivot_flat_same_cell__eliminate_two_cells K j i u v ltac:(lia) Hu Hv) in Hsame.
      destruct Hsame as [-> ->]. unfold left, right in *.
      rewrite !Z.eqb_refl, (proj2 (Z.eqb_neq v E) PreH55). reflexivity.
    - rewrite (proj2 (Z.eqb_neq _ _) Hother).
      assert (Hskip : andb (Z.eqb j i) (andb (Z.eqb u v) (negb (Z.eqb u E))) = false).
      { apply Bool.not_true_is_false. intro Hbad. apply andb_true_iff in Hbad.
        destruct Hbad as [Hj' Hu']. apply andb_true_iff in Hu'.
        destruct Hu' as [Hu' _]. apply Z.eqb_eq in Hj', Hu'. subst j u.
        exact (Hother eq_refl). }
      rewrite Hskip.
      destruct (Z.eqb (j*K+u) right) eqn:Hread; [|reflexivity].
      apply Z.eqb_eq in Hread.
      apply (pivot_flat_same_cell__eliminate_two_cells K j I u v ltac:(lia) Hu Hv) in Hread.
      destruct Hread as [-> ->].
      rewrite (PreH49 I v ltac:(lia) Hv), (proj2 (Z.eqb_neq I i) ltac:(lia)).
      reflexivity. }
  rewrite PreH13, <- PreH28, <- PreH51, <- PreH44, <- PreH45.
  fold left right T.
  Exists T Ac' Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - rewrite PreH19, PreH38.
    replace (AP + i*K*sizeof("__mpz_struct") + v*sizeof("__mpz_struct"))
      with (AP + left*sizeof("__mpz_struct")) by (unfold left; ring).
    replace (AP + I*K*sizeof("__mpz_struct") + v*sizeof("__mpz_struct"))
      with (AP + right*sizeof("__mpz_struct")) by (unfold right; ring).
    pose proof (pivot_merge_two_update__eliminate_two_cells AP (M*K) left right Ac_2
      T (Znth right Ab_2 0) Hleft Hright Hdifferent Hfirst Hmiddle) as Hmerge.
    unfold mpz_store, mpz_sizeof in Hmerge.
    sep_apply_l_atomic Hmerge.
    fold Ac'. sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia | congruence].
Qed.

Lemma proof_of_pivot_entail_wit_25_2 : pivot_entail_wit_25_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K,
    I_nonzero_pivot into I, E_nonzero_pivot into E, A_nonzero_pivot into A.
  assert (Hslot : 0 <= slot < Zlength Nn_2) by lia.
  assert (Hstep : pivot_elimination_slots M K I E i (slot+1) Mu_2 Nu_2 A Nn_2 Ab_2 Ac_2).
  { eapply pivot_elimination_slot_step__elimination_columns;
      [exact Hslot | exact PreH50 |].
    intros j u Hj Hu.
    rewrite <- PreH52, PreH1.
    destruct (Z.eqb j i), (Z.eqb u E); reflexivity. }
  Exists T_2 Ac_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia | congruence].
Qed.

Lemma proof_of_pivot_entail_wit_26 : pivot_entail_wit_26.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename K_nonzero_pivot into K, M_nonzero_pivot into M,
    I_nonzero_pivot into I, E_nonzero_pivot into E,
    AP_nonzero_pivot into AP.
  assert (Hslot : slot = K - M) by lia.
  subst slot.
  pose proof (PreH33 i ltac:(lia)) as Hrow.
  assert (Hdifferent : (i =? I)%Z = false) by (apply Z.eqb_neq; lia).
  rewrite Hdifferent, Z.ltb_irrefl in Hrow. cbn in Hrow.
  assert (Hslice : sublist (i*K) ((i+1)*K) Ab_2 =
    sublist (i*K) ((i+1)*K) A_nonzero_pivot).
  { unfold pivot_row_snapshot in Hrow. congruence. }
  assert (Hcoef : pivot_coef Ac_2 K i E =
    pivot_coef A_nonzero_pivot K i E).
  { rewrite (PreH50 i E) by lia.
    rewrite !Z.eqb_refl. cbn.
    rewrite <- !pivot_row_slice_coef by lia. now rewrite Hslice. }
  assert (Hidx : 0 <= i*K+E < M*K) by lia.
  Exists T_2 Ac_2 Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i AP (i*K+E) (M*K) Ac_2 0 Hidx).
    change (Znth (i*K+E) Ac_2 0) with (pivot_coef Ac_2 K i E).
    rewrite Hcoef.
    unfold mpz_store, mpz_sizeof.
    rewrite PreH39.
    replace (AP + (i*K+E)*sizeof("__mpz_struct"))
      with (AP + (i*K)*sizeof("__mpz_struct") + E*sizeof("__mpz_struct")) by ring.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_pivot_entail_wit_27 : pivot_entail_wit_27.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K,
    I_nonzero_pivot into I, E_nonzero_pivot into E,
    A_nonzero_pivot into A, D_nonzero_pivot into D,
    C_nonzero_pivot into C, B_nonzero_pivot into B,
    R_nonzero_pivot into R, N_nonzero_pivot into N,
    Q_nonzero_pivot into Q, AP_nonzero_pivot into AP,
    BP_nonzero_pivot into BP, RP_nonzero_pivot into RP,
    DP_nonzero_pivot into DP.
  set (Di := replace_Znth i (Mu_2 * Znth i D 0) Db_2).
  set (Ci := replace_Znth i (Mu_2 * Znth i C 0 + Nu_2 * Znth I Cb_2 0) Cb_2).
  set (Ai := replace_Znth (i*K+E) 0 Ac).
  prop_apply_p (UIntArray.full_Zlength BP M Bn_2).
  Intros_p HBn.
  prop_apply_p (UIntArray.full_Zlength RP K Rn_2).
  Intros_p HRn.
  prop_apply_p (MpzArray.full_Zlength DP M Di).
  Intros_p HDi.
  prop_apply_p (pivot_missing_slot_length__finish_elimination AP (i*K+E) (M*K) Ac).
  Intros_p HAc.
  assert (HB : Zlength B = M).
  { rewrite PreH26 in HBn. unfold pivot_basic in HBn.
    now rewrite Zlength_replace_Znth in HBn. }
  assert (HR : Zlength R = K).
  { rewrite PreH27 in HRn. unfold pivot_row_map in HRn.
    now rewrite !Zlength_replace_Znth in HRn. }
  assert (HD : Zlength Db_2 = M).
  { unfold Di in HDi. now rewrite Zlength_replace_Znth in HDi. }
  assert (Hraw : pivot_elimination_raw M K I E i Mu_2 Nu_2 D C A Db_2 Cb_2 Ab_2 Di Ci Ai
      /\ normalize_basic_zero K i Ai Bn_2).
  { subst b Bn_2 Rn_2 Nn_2.
    apply (pivot_elimination_slot_done__elimination_normalization M K I E i Q Mu_2 Nu_2
      D C A B R N Db_2 Cb_2 Ab_2 Ac); try assumption; lia. }
  destruct Hraw as [Hraw Hz].
  Exists T_2 Di Ci Ai Nu_2 Mu_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - rewrite PreH38.
    replace (AP + i*K*sizeof("__mpz_struct") + E*sizeof("__mpz_struct"))
      with (AP + (i*K+E)*sizeof("__mpz_struct")) by ring.
    change (store_Z (AP + (i*K+E)*sizeof("__mpz_struct")) 0)
      with (mpz_store AP (i*K+E) 0).
    sep_apply_l_atomic (MpzArray.missing_i_merge_to_full AP (i*K+E) (M*K) 0 Ac ltac:(lia)).
    fold Ai. fold Di Ci.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + unfold Di. rewrite Znth_replace_Znth_Same by lia.
      apply Z.mul_pos_pos; [assumption|].
      exact (proj2 (proj2 (proj1 PreH7 i ltac:(lia)))).
    + unfold Ai. now rewrite Zlength_replace_Znth.
Qed.

Lemma proof_of_pivot_entail_wit_28_1 : pivot_entail_wit_28_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename M_nonzero_pivot into M, K_nonzero_pivot into K,
    I_nonzero_pivot into I, E_nonzero_pivot into E,
    A_nonzero_pivot into A, D_nonzero_pivot into D,
    C_nonzero_pivot into C, B_nonzero_pivot into B,
    DP_nonzero_pivot into DP, CP_nonzero_pivot into CP.
  prop_apply_p (MpzArray.full_Zlength DP M Dn).
  Intros_p HDn.
  prop_apply_p (MpzArray.full_Zlength CP M Cn).
  Intros_p HCn.
  assert (Hdom : forall v, In v Nn_2 -> 0 <= v < K).
  { destruct PreH32 as [_ [_ [Hnonbasic _]]].
    intros v Hv. exact (proj1 (Hnonbasic v Hv)). }
  destruct (pivot_elimination_prefix_after_normalize__elimination_normalization
    M K I E i Mu_2 Nu_2 D C A B Nn_2 Db_2 Cb_2 Ab_2 Di Ci Ai Dn Cn An
    ltac:(lia) ltac:(lia) ltac:(lia) PreH38 Hdom PreH52 PreH53 PreH50
    HDn HCn PreH36 PreH44 PreH45 PreH46 PreH33 PreH48 PreH1) as [Hprefix Hdenom].
  Exists T_2 Nu_2 Mu_2
    (Z.gcd (Znth I Db_2 0) (pivot_coef A K i E))
    Dn Cn An Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - rewrite Hdenom.
    cancel (MpzArray.full CP M Cn).
    cancel (MpzArray.full DP M Dn).
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_pivot_entail_wit_28_2_split_goal_1 : pivot_entail_wit_28_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i.
  intros j Hj.
  rewrite (PreH34 j Hj).
  destruct (j =? I_nonzero_pivot)%Z eqn:Hr; [reflexivity|].
  apply Z.eqb_neq in Hr.
  assert (Htest : (j <? I_nonzero_pivot)%Z = (j <? I_nonzero_pivot + 1)%Z).
  { destruct (j <? I_nonzero_pivot)%Z eqn:Hlt.
    - symmetry. apply Z.ltb_lt in Hlt. apply Z.ltb_lt. lia.
    - symmetry. apply Z.ltb_ge in Hlt. apply Z.ltb_ge. lia. }
  now rewrite Htest.
Qed.

Lemma proof_of_pivot_entail_wit_28_2 : pivot_entail_wit_28_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pivot_entail_wit_28_2_split_goal_1.
Qed.

Lemma proof_of_pivot_entail_wit_28_3 : pivot_entail_wit_28_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename AP_nonzero_pivot into AP, M_nonzero_pivot into M,
    K_nonzero_pivot into K, I_nonzero_pivot into I, E_nonzero_pivot into E,
    D_nonzero_pivot into D, C_nonzero_pivot into C, A_nonzero_pivot into A,
    B_nonzero_pivot into B.
  pose proof (PreH4 PreH1) as Hzero.
  pose proof (PreH37 i ltac:(lia)) as Hrow.
  assert (Hother : (i =? I)%Z = false) by (apply Z.eqb_neq; lia).
  rewrite Hother, Z.ltb_irrefl in Hrow.
  change (pivot_row_snapshot K i Db_2 Cb_2 Ab_2 =
    pivot_row_snapshot K i D C A) in Hrow.
  pose proof (f_equal (@snd (Z * Z) (list Z)) Hrow) as Hslice.
  change (sublist (i * K) ((i + 1) * K) Ab_2 =
    sublist (i * K) ((i + 1) * K) A) in Hslice.
  apply (f_equal (fun row => Znth E row 0)) in Hslice.
  rewrite !pivot_row_slice_coef in Hslice by lia.
  change (Znth (i * K + E) Ab_2 0 = pivot_coef A K i E) in Hslice.
  sep_apply_l_atomic (store_Z_from_fields
    (ai + E * sizeof ("__mpz_struct")) EnterLimbs EnterSize EnterAlloc
    (pivot_coef A K i E) PreH2 PreH3).
  replace (ai + E * sizeof ("__mpz_struct"))
    with (AP + (i * K + E) * sizeof ("__mpz_struct")) by (rewrite PreH43; ring).
  change (store_Z (AP + (i * K + E) * sizeof ("__mpz_struct")) (pivot_coef A K i E))
    with (mpz_store AP (i * K + E) (pivot_coef A K i E)).
  sep_apply_l_atomic (MpzArray.missing_i_merge_to_full AP (i * K + E)
    (M * K) (pivot_coef A K i E) Ab_2 ltac:(lia)).
  rewrite <- Hslice, replace_Znth_Znth.
  Exists T_2 Nu_2 Mu_2 G_2 Db_2 Cb_2 Ab_2 Nn_2 Rn_2 Bn_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hji].
    + assert (Hnext : (i <? i + 1)%Z = true) by (apply Z.ltb_lt; lia).
      rewrite Hother, Hnext. cbn [orb].
      unfold pivot_final_row.
      destruct (pivot_normalized_row K I E D C A B Nn_2) as [[den constant] coefficients].
      rewrite Hother, Hzero, Z.eqb_refl.
      exact Hrow.
    + specialize (PreH37 j Hj).
      destruct (j <? i)%Z eqn:Hlt.
      * assert (Hnext : (j <? i + 1)%Z = true)
          by (apply Z.ltb_lt; apply Z.ltb_lt in Hlt; lia).
        now rewrite Hnext.
      * assert (Hnext : (j <? i + 1)%Z = false)
          by (apply Z.ltb_ge; apply Z.ltb_ge in Hlt; lia).
        now rewrite Hnext.
Qed.

Lemma proof_of_pivot_return_wit_1_split_goal_1 : pivot_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = M_nonzero_pivot) by lia. subst i.
  subst b Bn Rn Nn.
  apply pivot_final_rows_sound__final_result; assumption || lia.
Qed.

Lemma proof_of_pivot_return_wit_1 : pivot_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pivot_return_wit_1_split_goal_1.
Qed.

