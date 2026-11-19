From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.build_fme_model_input_revision_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Local Open Scope sac.

Lemma proof_of_build_entail_wit_1_split_goal_1 : build_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; unfold simplex_dimensions_ok in *; lia.
Qed.

Lemma proof_of_build_entail_wit_1_split_goal_spatial : build_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (Zsublist_nil Rows_initial_table 0 0) by lia.
  rewrite (sublist_self Rows_initial_table M_initial_table PreH2).
  sep_apply_r_atomic (build_empty_segment__build_initial_table head_pre (N_initial_table + 1)).
  cancel. all: reflexivity.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_build_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_2_split_goal_1 : build_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (build_tail_nonempty__build_initial_table q (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH7 ltac:(lia)).
  Intros_p Hlt.
  rewrite (build_suffix_cons__build_initial_table Rows_initial_table t_addr_rows M_initial_table PreH2 ltac:(lia)).
  cbn [build_input_segment].
  Intros_p Hnode. dump_pre_spatial. tauto.
Qed.

Lemma proof_of_build_entail_wit_2_split_goal_2 : build_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (build_tail_nonempty__build_initial_table q (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH7 ltac:(lia)).
  Intros_p Hlt.
  dump_pre_spatial. exact Hlt.
Qed.

Lemma proof_of_build_entail_wit_2_split_goal_spatial : build_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply_p (build_tail_nonempty__build_initial_table q (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH7 ltac:(lia)).
  Intros_p Hlt.
  rewrite (build_suffix_cons__build_initial_table Rows_initial_table t_addr_rows M_initial_table PreH2 ltac:(lia)).
  cbn [build_input_segment].
  Intros_p Hnode.
  cancel (&(q # "InequList" ->ₛ "next") # Ptr |->
    build_row_next (build_row_at Rows_initial_table t_addr_rows)).
  cancel. all: reflexivity.
Qed.

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_build_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; unfold simplex_dimensions_ok in PreH9;
    rewrite unsigned_last_nbits_eq by lia; lia.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_2 : build_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; unfold simplex_dimensions_ok in PreH9;
    rewrite unsigned_last_nbits_eq by lia; lia.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_spatial : build_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hbits : unsigned_last_nbits (seen + 1) 32 = seen + 1).
  { apply unsigned_last_nbits_eq. unfold simplex_dimensions_ok in PreH9.
     lia. }
  rewrite Hbits, PreH6, PreH8.
  cancel (build_input_segment (build_row_next (build_row_at Rows_initial_table seen))
    0 (N_initial_table + 1) (sublist (seen + 1) M_initial_table Rows_initial_table)).
  apply build_push_row__build_initial_table; [lia | exact PreH5 | congruence].
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_spatial.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_1 : build_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite sizeof_uint; unfold simplex_dimensions_ok in *; lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_2 : build_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite sizeof_uint; unfold simplex_dimensions_ok in *; lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_3 : build_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; rewrite sizeof_uint; unfold simplex_dimensions_ok in *; lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_4 : build_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (simplex_dimensions_mpz_bytes M_initial_table N_initial_table PreH5 PreH6); lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_5 : build_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (simplex_dimensions_mpz_bytes M_initial_table N_initial_table PreH5 PreH6); lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_6 : build_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (simplex_dimensions_mpz_bytes M_initial_table N_initial_table PreH5 PreH6); lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_7 : build_entail_wit_4_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (simplex_dimensions_bounds M_initial_table N_initial_table PreH5); lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_8 : build_entail_wit_4_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; pose proof (simplex_dimensions_bounds M_initial_table N_initial_table PreH5); lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_9 : build_entail_wit_4_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; unfold simplex_dimensions_ok in *; lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_10 : build_entail_wit_4_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; unfold simplex_dimensions_ok in *; lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_11 : build_entail_wit_4_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q.
  prop_apply_p (build_tail_null__build_initial_table (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH2 ltac:(lia)).
  Intros_p Hrows.
  dump_pre_spatial. exact Hrows.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_12 : build_entail_wit_4_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q.
  prop_apply_p (build_tail_null__build_initial_table (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH2 ltac:(lia)).
  Intros_p Hrows.
  dump_pre_spatial. rewrite Hrows.
  unfold simplex_dimensions_ok in PreH5.
  rewrite unsigned_last_nbits_eq by lia.
  lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_13 : build_entail_wit_4_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q.
  prop_apply_p (build_tail_null__build_initial_table (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH2 ltac:(lia)).
  Intros_p Hrows.
  dump_pre_spatial. rewrite Hrows.
  unfold simplex_dimensions_ok in PreH5.
  rewrite unsigned_last_nbits_eq by lia.
  lia.
Qed.

Lemma proof_of_build_entail_wit_4_split_goal_spatial : build_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q.
  prop_apply_p (build_tail_null__build_initial_table (N_initial_table + 1)
    Rows_initial_table t_addr_rows M_initial_table PreH2 ltac:(lia)).
  Intros_p Hrows.
  rewrite Hrows, (sublist_self Rows_initial_table M_initial_table PreH2).
  rewrite (Zsublist_nil Rows_initial_table M_initial_table M_initial_table) by lia.
  cbn [build_input_segment]. Intros_p Hempty.
  cancel. all: reflexivity.
Qed.

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_spatial.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_6.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_7.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_8.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_9.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_10.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_11.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_12.
  - Goal_apply proof_of_build_entail_wit_4_split_goal_13.
Qed.

Lemma proof_of_build_entail_wit_5_split_goal_1 : build_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: intros; lia.
Qed.

Lemma proof_of_build_entail_wit_5_split_goal_spatial : build_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst t_addr_cols_2.
  rewrite sizeof_uint in *.
  assert (Hm : 0 <= M_initial_table) by lia.
  assert (Hn : 0 <= N_initial_table) by lia.
  assert (Hk : 0 <= M_initial_table + N_initial_table) by lia.
  assert (Hbasic : 0 < M_initial_table ->
    0 <= retval_4 /\ (4 | retval_4) /\ retval_4 + 4*M_initial_table - 1 <= addr_max_unsigned).
  { intro Hpos.
    destruct (PreH9 ltac:(lia)) as [[Hnonnull Halign] Hlast].
    split; [lia|]. split; [exists align4; lia|].
    change (retval_4 + 4*M_initial_table - 1 <= UINT_MAX). lia. }
  assert (Hrow : 0 < M_initial_table + N_initial_table ->
    0 <= retval_5 /\ (4 | retval_5) /\ retval_5 + 4*(M_initial_table+N_initial_table) - 1 <= addr_max_unsigned).
  { intro Hpos.
    destruct (PreH6 ltac:(lia)) as [[Hnonnull Halign] Hlast].
    split; [lia|]. split; [exists align4_2; lia|].
    change (retval_5 + 4*(M_initial_table+N_initial_table) - 1 <= UINT_MAX). lia. }
  assert (Hnb : 0 < N_initial_table ->
    0 <= retval_6 /\ (4 | retval_6) /\ retval_6 + 4*N_initial_table - 1 <= addr_max_unsigned).
  { intro Hpos.
    destruct (PreH3 ltac:(lia)) as [[Hnonnull Halign] Hlast].
    split; [lia|]. split; [exists align4_3; lia|].
    change (retval_6 + 4*N_initial_table - 1 <= UINT_MAX). lia. }
  replace (M_initial_table * 4) with (4*M_initial_table) by lia.
  replace ((M_initial_table + N_initial_table) * 4) with (4*(M_initial_table+N_initial_table)) by lia.
  replace (N_initial_table * 4) with (4*N_initial_table) by lia.
  sep_apply_l_atomic (build_uchar_to_uint_full__build_initial_table retval_4 M_initial_table Hm Hbasic).
  sep_apply_l_atomic (build_uchar_to_uint_full__build_initial_table retval_5 (M_initial_table+N_initial_table) Hk Hrow).
  sep_apply_l_atomic (build_uchar_to_uint_full__build_initial_table retval_6 N_initial_table Hn Hnb).
  sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg retval_6 N_initial_table).
  cancel.
Qed.

Lemma proof_of_build_entail_wit_5 : build_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_5_split_goal_spatial.
  - Goal_apply proof_of_build_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_1 : build_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: intros; lia.
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_2 : build_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (pose proof (simplex_dimensions_bounds _ _ PreH5) as Hbounds;
        unfold simplex_dimensions_ok in PreH5; lia).
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_3 : build_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (pose proof (simplex_dimensions_bounds _ _ PreH5) as Hbounds;
        unfold simplex_dimensions_ok in PreH5; lia).
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_4 : build_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (pose proof (simplex_dimensions_bounds _ _ PreH5) as Hbounds;
        unfold simplex_dimensions_ok in PreH5; lia).
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_5 : build_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (pose proof (simplex_dimensions_bounds _ _ PreH5) as Hbounds;
        unfold simplex_dimensions_ok in PreH5; lia).
Qed.

Lemma proof_of_build_entail_wit_7_split_goal_6 : build_entail_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: (intros; eapply PreH10; lia).
Qed.

Lemma proof_of_build_entail_wit_7 : build_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_5.
  - Goal_apply proof_of_build_entail_wit_7_split_goal_6.
Qed.

Lemma proof_of_build_entail_wit_9 : build_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hv : v = M_initial_table + N_initial_table) by lia.
  subst v.
  rewrite Zsublist_nil by lia. rewrite sublist_self by lia.
  set (k := M_initial_table + N_initial_table) in *.
  assert (Hmk : 0 <= M_initial_table*k) by (unfold k; nia).
  assert (Hprefix : simplex_build_prefix N_initial_table k 0 0 0
    (build_matrix Rows_initial_table) (repeat 0 (Z.to_nat M_initial_table))
    (repeat 0 (Z.to_nat M_initial_table)) (repeat 0 (Z.to_nat (M_initial_table*k))) nil rowVals_2).
  { unfold k. apply build_prefix_initial__build_initial_table; lia || assumption. }
  Exists (repeat 0 (Z.to_nat M_initial_table)) (repeat 0 (Z.to_nat M_initial_table))
    (repeat 0 (Z.to_nat (M_initial_table*k))) (@nil Z) rowVals_2 nbVals_2 nbPtr_2
    rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 t_addr_cols_2.
  split_pure_spatial.
  - sep_apply_l_atomic (build_dummy_zero_array__build_initial_table dPtr_2 M_initial_table (&("mpz_dummy_limb")) ltac:(lia)).
    sep_apply_l_atomic (build_dummy_zero_array__build_initial_table cPtr_2 M_initial_table (&("mpz_dummy_limb")) ltac:(lia)).
    sep_apply_l_atomic (build_dummy_zero_array__build_initial_table aPtr_2 (M_initial_table*k) (&("mpz_dummy_limb")) Hmk).
    rewrite (UIntArray.undef_seg_empty rowPtr_2 k).
    sep_apply_l_atomic (UIntArray.undef_full_to_undef_seg bPtr_2 M_initial_table).
    change (UIntArray.seg rowPtr_2 0 k rowVals_2) with (UIntArray.full rowPtr_2 k rowVals_2).
    sep_apply_r_atomic (build_empty_segment__build_initial_table head_pre (N_initial_table + 1)).
    rewrite (UIntArray.seg_empty bPtr_2 0 0).
    sepcon_assoc_change. cancel.
    split_pure_spatial; [cancel | dump_pre_spatial; reflexivity].
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | unfold k in *; lia].
Qed.

Lemma proof_of_build_entail_wit_10 : build_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (build_suffix_cons__build_initial_table Rows_initial_table r M_initial_table ltac:(lia) ltac:(lia)).
  cbn [build_input_segment]. Intros_p Hnode.
  destruct Hnode as [Hq Hcoef].
  set (coef := build_row_coefficients (build_row_at Rows_initial_table r)) in *.
  set (entries := build_row_entries (build_row_at Rows_initial_table r)) in *.
  prop_apply (MpzArray.full_Zlength dPtr_2 M_initial_table dVals_2). Intros_p Hdlen.
  assert (Hz : Znth r dVals_2 0 = 0).
  { match goal with H : simplex_build_prefix _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 H r ltac:(lia)) as Hread end.
    rewrite Z.ltb_irrefl in Hread. exact Hread. }
  pose proof (MpzArray.full_split_to_missing_i dPtr_2 r M_initial_table dVals_2 0 ltac:(lia)) as Hsplit.
  rewrite Hz in Hsplit. unfold mpz_store, mpz_sizeof in Hsplit. sep_apply_l_atomic Hsplit.
  Exists dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2
    (build_row_next (build_row_at Rows_initial_table r)) coef nbVals_2 nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 t_addr_cols_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_entail_wit_11 : build_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q_coef_2.
  set (coef := build_row_coefficients (build_row_at Rows_initial_table r)) in *.
  set (entries := build_row_entries (build_row_at Rows_initial_table r)) in *.
  prop_apply (MpzArray.full_Zlength cPtr_2 M_initial_table cVals_2). Intros_p Hclen.
  assert (Hz : Znth r cVals_2 0 = 0).
  { match goal with H : simplex_build_prefix _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 (proj2 H) r ltac:(lia)) as Hread end.
    rewrite Z.ltb_irrefl in Hread. exact Hread. }
  pose proof (MpzArray.full_split_to_missing_i cPtr_2 r M_initial_table cVals_2 0 ltac:(lia)) as Hsplit.
  rewrite Hz in Hsplit. unfold mpz_store, mpz_sizeof in Hsplit. sep_apply_l_atomic Hsplit.
  pose proof (MpzArray.full_split_to_missing_i coef 0 (N_initial_table+1) entries 0 ltac:(lia)) as Hsource.
  unfold mpz_store in Hsource. replace (coef + 0 * mpz_sizeof) with coef in Hsource by lia.
  sep_apply_l_atomic Hsource.
  Exists dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 q_next_2 coef nbVals_2 nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 t_addr_cols_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_entail_wit_12 : build_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q_coef_2.
  prop_apply (build_missing_length__build_initial_table dPtr_2 r M_initial_table dVals_2).
  Intros_p Hdlen.
  prop_apply (build_missing_length__build_initial_table cPtr_2 r M_initial_table cVals_2).
  Intros_p Hclen.
  pose proof (build_dc_prefix_step__build_initial_table N_initial_table
    (M_initial_table + N_initial_table) r Rows_initial_table dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption)) as Hprefix.
  set (coef := build_row_coefficients (build_row_at Rows_initial_table r)) in *.
  set (entries := build_row_entries (build_row_at Rows_initial_table r)) in *.
  pose proof (build_input_coefficients_restore coef 0 (N_initial_table + 1) entries ltac:(lia)) as Hrestore.
  replace (coef + 0 * mpz_sizeof) with coef in Hrestore by lia.
  sep_apply_l_atomic Hrestore.
  Exists (replace_Znth r 1 dVals_2) (replace_Znth r (Znth 0 entries 0) cVals_2)
    aVals_2 bVals_2 rowVals_2 q_next_2 coef nbVals_2 nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 t_addr_cols_2.
  split_pure_spatial.
  - set (dval := 1) in *.
    pose proof (MpzArray.missing_i_merge_to_full dPtr_2 r M_initial_table dval dVals_2 ltac:(lia)) as Hdmerge.
    pose proof (MpzArray.missing_i_merge_to_full cPtr_2 r M_initial_table (Znth 0 entries 0) cVals_2 ltac:(lia)) as Hcmerge.
    unfold mpz_store, mpz_sizeof in Hdmerge, Hcmerge.
    sep_apply_l_atomic Hdmerge.
    sep_apply_l_atomic Hcmerge.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_entail_wit_13 : build_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q_coef_2 t_addr_cols_2.
  set (k := M_initial_table + N_initial_table) in *.
  assert (Hrow : 0 <= r*k <= INT_MAX).
  { split.
    - unfold k. apply Z.mul_nonneg_nonneg; lia.
    - eapply Z.le_trans with (m := M_initial_table*k).
      + apply Z.mul_le_mono_nonneg_r; unfold k; lia.
      + unfold k. assumption. }
  set (coef := build_row_coefficients (build_row_at Rows_initial_table r)) in *.
  set (entries := build_row_entries (build_row_at Rows_initial_table r)) in *.
  assert (Hz : Znth (r*k+v) aVals_2 0 = 0).
  { match goal with H : simplex_build_prefix _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 (proj2 (proj2 H)) r v
        ltac:(rewrite build_matrix_length__build_initial_table; lia) ltac:(unfold k; lia)) as Hread end.
    rewrite !Z.ltb_irrefl, Z.eqb_refl in Hread. exact Hread. }
  assert (Hindex : 0 <= r*k+v < M_initial_table*k).
  { unfold k. apply simplex_dimensions_index; try assumption; lia. }
  pose proof (MpzArray.full_split_to_missing_i aPtr_2 (r*k+v) (M_initial_table*k)
    aVals_2 0 Hindex) as Hsplit.
  rewrite Hz in Hsplit. unfold mpz_store, mpz_sizeof in Hsplit. sep_apply_l_atomic Hsplit.
  pose proof (MpzArray.full_split_to_missing_i coef (v+1) (N_initial_table+1) entries 0 ltac:(lia)) as Hsource.
  unfold mpz_store, mpz_sizeof in Hsource. sep_apply_l_atomic Hsource.
  Exists dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 q_next_2 coef nbVals_2 nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 k.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | unfold k in *; nia].
Qed.

Lemma proof_of_build_entail_wit_14 : build_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q_coef_2 t_addr_cols_2.
  set (k := M_initial_table + N_initial_table) in *.
  set (coef := build_row_coefficients (build_row_at Rows_initial_table r)) in *.
  set (entries := build_row_entries (build_row_at Rows_initial_table r)) in *.
  prop_apply (build_missing_length__build_initial_table aPtr_2 (r*k+v) (M_initial_table*k) aVals_2).
  Intros_p Halen.
  pose proof (build_a_prefix_step__build_initial_table N_initial_table k r v Rows_initial_table
    dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(replace (Zlength Rows_initial_table) with M_initial_table by lia; lia)
    ltac:(assumption)) as Hprefix.
  pose proof (build_input_coefficients_restore coef (v+1) (N_initial_table+1) entries ltac:(lia)) as Hrestore.
  unfold mpz_sizeof in Hrestore. sep_apply_l_atomic Hrestore.
  Exists dVals_2 cVals_2 (replace_Znth (r*k+v) (Znth (v+1) entries 0) aVals_2)
    bVals_2 rowVals_2 q_next_2 coef nbVals_2 nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 k.
  assert (Hindex : 0 <= r*k+v < M_initial_table*k).
  { unfold k. apply simplex_dimensions_index; try assumption; lia. }
  split_pure_spatial.
  - pose proof (MpzArray.missing_i_merge_to_full aPtr_2 (r*k+v)
      (M_initial_table*k) (Znth (v+1) entries 0) aVals_2 Hindex) as Hamerge.
    unfold mpz_store, mpz_sizeof in Hamerge.
    sep_apply_l_atomic Hamerge.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_entail_wit_15 : build_entail_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hv : v = N_initial_table) by lia.
  subst v q_next q_coef.
  prop_apply (UIntArray.seg_Zlength bPtr_2 0 (r+1) (app bVals_2 (cons (N_initial_table+r) nil))).
  Intros_p Hbl.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hbl.
  prop_apply (UIntArray.full_Zlength rowPtr_2 (M_initial_table+N_initial_table)
    (replace_Znth (N_initial_table+r) r rowVals_2)).
  Intros_p Hrl. rewrite Zlength_replace_Znth in Hrl.
  pose proof (build_outer_prefix_step__build_initial_table N_initial_table M_initial_table r Rows_initial_table
    dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 ltac:(lia) ltac:(lia) ltac:(lia) Hrl ltac:(assumption)) as Hprefix.
  Exists dVals_2 cVals_2 aVals_2 (app bVals_2 (cons (N_initial_table+r) nil)) (replace_Znth (N_initial_table+r) r rowVals_2)
    nbVals_2 nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 t_addr_cols_2.
  split_pure_spatial.
  - pose proof (build_push_row__build_initial_table Rows_initial_table r head_pre q (N_initial_table+1)
      ltac:(lia) ltac:(lia) ltac:(lia)) as Hpush.
    sepcon_assoc_change. cancel.
    sep_apply_r_atomic Hpush.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hr : r = M_initial_table) by lia.
  subst r.
  prop_apply (MpzArray.full_Zlength dPtr_2 M_initial_table dVals_2). Intros_p Hdlen.
  prop_apply (MpzArray.full_Zlength cPtr_2 M_initial_table cVals_2). Intros_p Hclen.
  pose proof (build_prefix_final__build_initial_table N_initial_table M_initial_table Rows_initial_table
    dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 ltac:(lia) ltac:(lia) ltac:(lia) Hdlen Hclen ltac:(assumption))
    as Htable.
  pose proof (simplex_initial_table_implies_rational_equations N_initial_table M_initial_table
    (M_initial_table+N_initial_table) (build_matrix Rows_initial_table) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2
    ltac:(lia) ltac:(lia) Htable) as Hequations.
  Exists nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 t_addr_cols
    dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 nbVals_2.
  split_pure_spatial.
  - sep_apply (build_input_segment_app (sublist 0 M_initial_table Rows_initial_table)
      (sublist M_initial_table M_initial_table Rows_initial_table) head_pre q 0 (N_initial_table+1)).
    rewrite <- (sublist_split 0 M_initial_table M_initial_table Rows_initial_table) by lia.
    rewrite sublist_self by lia.
    change (UIntArray.seg bPtr_2 0 M_initial_table bVals_2) with (UIntArray.full bPtr_2 M_initial_table bVals_2).
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

