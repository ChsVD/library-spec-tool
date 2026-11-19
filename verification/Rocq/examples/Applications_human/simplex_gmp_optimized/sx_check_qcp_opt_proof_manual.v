From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import sx_check_qcp_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import sx_check_qcp_opt_proof_auto.
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

Lemma proof_of_sx_check_qcp_entail_wit_1 : sx_check_qcp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hm0 : 0 <= M_rational_feasibility_normal).
  { rewrite PreH2. apply Zlength_nonneg. }
  Exists 0.
  split_pure_spatial.
  - subst variables_pre.
    rewrite Zsublist_nil, sublist_self by lia.
    cbn [build_input_segment].
    sepcon_assoc_change. cancel.
    try (split_pure_spatial; [cancel | dump_pre_spatial; reflexivity]).
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_2 : sx_check_qcp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH2 as (_ & Hn & _).
  prop_apply (build_tail_nonempty__build_initial_table q
    (N_rational_feasibility_normal + 1) Rows_rational_feasibility_normal i_2
    M_rational_feasibility_normal PreH7 ltac:(lia)).
  Intros_p Hi.
  rewrite (build_suffix_cons__build_initial_table Rows_rational_feasibility_normal
    i_2 M_rational_feasibility_normal PreH1 ltac:(lia)).
  cbn [build_input_segment].
  Intros_p Hnode.
  set (row := build_row_at Rows_rational_feasibility_normal i_2) in *.
  pose proof (MpzArray.full_split_to_missing_i (build_row_coefficients row) 0
    (N_rational_feasibility_normal + 1) (build_row_entries row) 0 ltac:(lia)) as Hsplit.
  unfold mpz_store in Hsplit.
  rewrite Z.mul_0_l, Z.add_0_r in Hsplit.
  sep_apply Hsplit.
  sep_apply (os_mpz_size_open (build_row_coefficients row) (Znth 0 (build_row_entries row) 0)).
  Intros size.
  Exists size (build_row_next row) (build_row_coefficients row) i_2.
  unfold row.
  split_pure_spatial.
  - rewrite Z.mul_0_l, Z.add_0_r.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | tauto | lia].
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_3 : sx_check_qcp_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (n := N_rational_feasibility_normal) in *.
  set (row := build_row_at Rows_rational_feasibility_normal i_2) in *.
  assert (Hn : 0 <= n) by (unfold simplex_dimensions_ok in PreH3; tauto).
  assert (Hpositive : 0 < Znth 0 (build_row_entries row) 0).
  { unfold os_size_relation in PreH12.
    rewrite Z.sgn_pos in PreH12 by lia.
    apply Z.sgn_pos_iff. symmetry. exact PreH12. }
  replace (coef_2 + 0 * sizeof("__mpz_struct")) with coef_2 by ring.
  sep_apply (os_mpz_size_close coef_2 (Znth 0 (build_row_entries row) 0) sz_2).
  pose proof (build_input_coefficients_restore coef_2 0 (n + 1)
    (build_row_entries row) ltac:(lia)) as Hrestore.
  replace (coef_2 + 0 * mpz_sizeof) with coef_2 in Hrestore by ring.
  sep_apply Hrestore.
  destruct (Z.eq_dec n 0) as [Hempty | Hnonempty].
  - rewrite Hempty in PreH3 |- *.
    Left. Exists next_2 coef_2 i_2.
    unfold row in *.
    split_pure_spatial; [sepcon_assoc_change; cancel |].
    split_pures; dump_pre_spatial; try assumption; try lia.
    apply sx_zero_prefix_start.
  - sep_apply (MpzArray.full_split_to_missing_i coef_2 1 (n + 1)
      (build_row_entries row) 0 ltac:(lia)).
    unfold mpz_store.
    change (Znth 1 (build_row_entries row) 0) with (os_coef row 0).
    sep_apply (os_mpz_size_open (coef_2 + 1 * mpz_sizeof) (os_coef row 0)).
    Intros size.
    Right. Exists size 0 next_2 coef_2 i_2.
    replace (0 + 1) with 1 by reflexivity.
    unfold row in *.
    split_pure_spatial; [unfold mpz_sizeof; sepcon_assoc_change; cancel |].
    split_pures; dump_pre_spatial; try assumption; try lia.
    apply sx_zero_prefix_start.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_4 : sx_check_qcp_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (n := N_rational_feasibility_normal) in *.
  set (row := build_row_at Rows_rational_feasibility_normal i_2) in *.
  assert (Hzero : os_coef row j_2 = 0).
  { unfold os_size_relation in PreH18.
    rewrite PreH1 in PreH18.
    apply Z.sgn_null_iff. symmetry. exact PreH18. }
  pose proof (sx_zero_prefix_step row j_2 PreH16 Hzero) as Hprefix.
  fold mpz_sizeof.
  sep_apply (os_mpz_size_close (coef_2 + (j_2 + 1) * mpz_sizeof)
    (os_coef row j_2) sz_2).
  unfold os_coef at 1.
  sep_apply (build_input_coefficients_restore coef_2 (j_2 + 1) (n + 1)
    (build_row_entries row) ltac:(lia)).
  destruct (Z.eq_dec (j_2 + 1) n) as [Hdone | Hmore].
  - rewrite Hdone in Hprefix |- *.
    Left. Exists next_2 coef_2 i_2.
    unfold row in *.
    split_pure_spatial; [sepcon_assoc_change; cancel |].
    split_pures; dump_pre_spatial; assumption || lia.
  - sep_apply (MpzArray.full_split_to_missing_i coef_2 ((j_2 + 1) + 1) (n + 1)
      (build_row_entries row) 0 ltac:(lia)).
    unfold mpz_store.
    change (Znth ((j_2 + 1) + 1) (build_row_entries row) 0)
      with (os_coef row (j_2 + 1)).
    sep_apply (os_mpz_size_open (coef_2 + ((j_2 + 1) + 1) * mpz_sizeof)
      (os_coef row (j_2 + 1))).
    Intros size.
    Right. Exists size (j_2 + 1) next_2 coef_2 i_2.
    unfold row in *.
    split_pure_spatial; [sepcon_assoc_change; cancel |].
    split_pures; dump_pre_spatial; assumption || lia.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_5_1 : sx_check_qcp_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst next coef.
  set (row := build_row_at Rows_rational_feasibility_normal i_2) in *.
  pose proof (os_mpz_size_close (build_row_coefficients row + (j + 1) * mpz_sizeof)
    (os_coef row j) sz) as Hclose.
  unfold mpz_sizeof in Hclose.
  sep_apply Hclose.
  unfold os_coef.
  pose proof (build_input_coefficients_restore (build_row_coefficients row) (j + 1)
    (N_rational_feasibility_normal + 1) (build_row_entries row) ltac:(lia)) as Hrestore.
  unfold mpz_sizeof in Hrestore.
  sep_apply Hrestore.
  Exists (i_2 + 1).
  split_pure_spatial.
  - unfold row.
    cancel (build_input_segment (build_row_next (build_row_at Rows_rational_feasibility_normal i_2))
      0 (N_rational_feasibility_normal + 1)
      (sublist (i_2 + 1) M_rational_feasibility_normal Rows_rational_feasibility_normal)).
    sep_apply_r_atomic (build_push_row__build_initial_table Rows_rational_feasibility_normal i_2
      head_pre q (N_rational_feasibility_normal + 1) ltac:(lia) ltac:(assumption) ltac:(assumption)).
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_5_2 : sx_check_qcp_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH3 as (_ & Hn & _).
  subst next coef.
  set (row := build_row_at Rows_rational_feasibility_normal i_2) in *.
  rewrite Z.mul_0_l, Z.add_0_r.
  sep_apply (os_mpz_size_close (build_row_coefficients row)
    (Znth 0 (build_row_entries row) 0) sz).
  pose proof (build_input_coefficients_restore (build_row_coefficients row) 0
    (N_rational_feasibility_normal + 1) (build_row_entries row) ltac:(lia)) as Hrestore.
  rewrite Z.mul_0_l, Z.add_0_r in Hrestore.
  sep_apply Hrestore.
  Exists (i_2 + 1).
  split_pure_spatial.
  - unfold row.
    cancel (build_input_segment (build_row_next (build_row_at Rows_rational_feasibility_normal i_2))
      0 (N_rational_feasibility_normal + 1)
      (sublist (i_2 + 1) M_rational_feasibility_normal Rows_rational_feasibility_normal)).
    sep_apply_r_atomic (build_push_row__build_initial_table Rows_rational_feasibility_normal i_2
      head_pre q (N_rational_feasibility_normal + 1) ltac:(lia) ltac:(assumption) ltac:(assumption)).
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_6_split_goal_spatial : sx_check_qcp_entail_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst q.
  sep_apply (build_input_segment_app (sublist 0 i Rows_rational_feasibility_normal)
    (sublist i M_rational_feasibility_normal Rows_rational_feasibility_normal)
    head_pre 0 0 (N_rational_feasibility_normal + 1)).
  rewrite <- (sublist_split 0 M_rational_feasibility_normal i Rows_rational_feasibility_normal) by lia.
  rewrite sublist_self by lia. cancel.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_6 : sx_check_qcp_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_check_qcp_entail_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_7_split_goal_1 : sx_check_qcp_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_check_qcp_entail_wit_7_split_goal_2 : sx_check_qcp_entail_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_check_qcp_entail_wit_7_split_goal_3 : sx_check_qcp_entail_wit_7_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_check_qcp_entail_wit_7_split_goal_4 : sx_check_qcp_entail_wit_7_split_goal_4.
Proof. Abort.

Lemma proof_of_sx_check_qcp_entail_wit_7_split_goal_5 : sx_check_qcp_entail_wit_7_split_goal_5.
Proof. Abort.

Lemma proof_of_sx_check_qcp_entail_wit_7 : sx_check_qcp_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_rows retval_cols M_rational_feasibility_normal.
  rename N_rational_feasibility_normal into n.
  set (m := Zlength (os_kept n Rows_rational_feasibility_normal)) in *.
  prop_apply_p (UIntArray.full_Zlength bPtr m bVals).
  Intros_p Hbasic_length.
  prop_apply_p (UIntArray.full_Zlength nbPtr n nbVals).
  Intros_p Hnonbasic_length.
  pose proof (os_kept_length n Rows_rational_feasibility_normal) as Hkept.
  fold m in Hkept.
  pose proof (simplex_dimensions_smaller _ _ _ PreH7 Hkept) as Hdim.
  pose proof (proj1 (proj2 Hdim)) as Hn.
  pose proof (proj1 (proj2 (proj2 Hdim))) as Hmax.
  Exists nbPtr rowPtr bPtr aPtr cPtr dPtr cVals nbVals dVals aVals bVals rowVals (m + n) m.
  split_pure_spatial.
  - repeat (progress cancel).
  - split_pures; dump_pre_spatial; try reflexivity.
    + exact Hdim.
    + intros Hpositive. apply PreH8. lia.
    + eapply sx_initial_selection_basis; eassumption.
    + destruct PreH2 as (_ & Hrows & Hprefix & _).
      assert (Hbasic_range : forall v, In v bVals <-> n <= v < m + n).
      {
        intros v; split.
        - intros Hin.
          destruct (In_nth bVals v 0 Hin) as [i [Hi Hnth]].
          assert (Hindex : 0 <= Z.of_nat i < m).
          { rewrite <- Hbasic_length, Zlength_correct. lia. }
          destruct (Hrows _ Hindex) as (_ & _ & Hbasic & _).
          unfold Znth in Hbasic. rewrite Nat2Z.id, Hnth in Hbasic. lia.
        - intros Hv.
          assert (Hindex : 0 <= v - n < m) by lia.
          destruct (Hrows _ Hindex) as (_ & _ & Hbasic & _).
          replace v with (Znth (v - n) bVals 0) at 1 by lia.
          apply SumLib.ZRange.Znth_In_Zlength. now rewrite Hbasic_length.
      }
      assert (Hnonbasic_nth : forall i, (i < length nbVals)%nat ->
        nth i nbVals 0 = Z.of_nat i).
      {
        intros i Hi.
        assert (Hindex : 0 <= Z.of_nat i < n).
        { rewrite <- Hnonbasic_length, Zlength_correct. lia. }
        specialize (PreH1 _ Hindex). unfold Znth in PreH1.
        now rewrite Nat2Z.id in PreH1.
      }
      assert (Hnonbasic_range : forall v, In v nbVals <-> 0 <= v < n).
      {
        intros v; split.
        - intros Hin.
          destruct (In_nth nbVals v 0 Hin) as [i [Hi Hnth]].
          rewrite Hnonbasic_nth in Hnth by exact Hi.
          rewrite <- Hnth, <- Hnonbasic_length, Zlength_correct. lia.
        - intros Hv.
          rewrite <- (PreH1 v Hv) at 1.
          apply SumLib.ZRange.Znth_In_Zlength. now rewrite Hnonbasic_length.
      }
      unfold pivot_nonbasic_columns, normalize_opt_lib.normalize_columns.
      split.
      * split.
        -- apply (proj2 (NoDup_nth nbVals 0)).
           intros i j Hi Hj Heq.
           rewrite (Hnonbasic_nth i Hi), (Hnonbasic_nth j Hj) in Heq. lia.
        -- split.
           ++ intros v Hv. apply Hbasic_range in Hv. lia.
           ++ split.
              ** intros v Hv. apply Hnonbasic_range in Hv.
                 split; [lia | now apply Hprefix].
              ** intros v Hv. destruct (Z_lt_ge_dec v n).
                 --- right. apply Hnonbasic_range. lia.
                 --- left. apply Hbasic_range. lia.
      * intros v Hv. rewrite Hnonbasic_range. split.
        -- apply Hprefix.
        -- intros Htag.
           destruct (Z_lt_ge_dec v n) as [Horiginal|Hbasic]; [lia|].
           assert (Hindex : 0 <= v - n < m) by lia.
           destruct (Hrows _ Hindex) as (_ & _ & _ & Hmap).
           replace (n + (v - n)) with v in Hmap by lia.
           lia.
    + now apply sx_initial_selection_equations.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_8 : sx_check_qcp_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (scan_mpz_array_bridge DP_2 P_2 D_2).
  rewrite (scan_mpz_array_bridge CP_2 P_2 C_2).
  rewrite (scan_mpz_array_bridge AP_2 (P_2 * K_2) A_2).
  Intros DT CT AT.
  Exists AT CT DT.
  Exists NP_2 RP_2 BP_2 AP_2 CP_2 DP_2 C_2 NB_2 D_2 A_2 B_2 R_2 K_2 P_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_9 : sx_check_qcp_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (0 <= N_rational_feasibility_normal) as Hvariables
    by (unfold simplex_dimensions_ok in PreH13; lia).
  pose proof (proj1 (valid_selection_first_aux N_rational_feasibility_normal
    K_2 P_2 D_2 C_2 A_2 B_2 R_2 retval Hvariables PreH5 PreH6 PreH8)) as Hrow.
  destruct (proj1 (first_entering_minimal N_rational_feasibility_normal K_2 R_2
    (entering_row retval K_2 (scan_row_values A_2)) retval_2 PreH1) PreH3)
    as (Hcolumn & Hcandidate & _).
  pose proof (proj1 Hcandidate) as Hnonbasic.
  pose proof (entering_candidate_nonzero N_rational_feasibility_normal R_2
    (entering_row retval K_2 (scan_row_values A_2)) retval_2 Hcandidate) as Hcoef.
  change (pivot_coef A_2 K_2 retval retval_2 <> 0) in Hcoef.
  pose proof (sx_entering_slot_valid K_2 B_2 R_2 NB_2 retval_2
    PreH16 Hcolumn Hnonbasic) as Hslot.
  pose proof (PreH14 ltac:(lia)) as Hlayout.
  prop_apply_p (UIntArray.full_Zlength NP_2 N_rational_feasibility_normal NB_2).
  Intros_p Hlength.
  Exists NP_2 RP_2 BP_2 AP_2 CP_2 DP_2 C_2 NB_2 D_2 A_2 B_2 R_2 K_2 P_2.
  replace (K_2 - P_2) with N_rational_feasibility_normal by lia.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge DP_2 P_2 D_2)).
    Exists DT.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge CP_2 P_2 C_2)).
    Exists CT.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge AP_2 (P_2 * K_2) A_2)).
    Exists AT.
    sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_10 : sx_check_qcp_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (sx_pivot_preserves_selection_equations N_rational_feasibility_normal
    P_2 K_2 (build_matrix (os_kept N_rational_feasibility_normal Rows_rational_feasibility_normal))
    r e (sx_entering_slot NB_2 e) D_2 C_2 A_2 B_2 R_2 NB_2 Df Cf Af Bf Rf Nf
    PreH11 PreH2) as Hequations.
  destruct PreH2 as (_ & _ & _ & _ & Hbasis & Hcolumns & _ & _).
  replace (K_2 - P_2) with N_rational_feasibility_normal in * by lia.
  Exists NP_2 RP_2 BP_2 AP_2 CP_2 DP_2 Cf Nf Df Af Bf Rf K_2 P_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_11_1 : sx_check_qcp_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH8 as Hdimensions.
  destruct Hdimensions as (HP & HN & HKmax & _).
  assert (HK : 0 <= K) by lia.
  Exists A_2 C_2 D_2 NP_2 RP_2 BP_2 AP_2 CP_2 DP_2 K P_2.
  split_pure_spatial.
  - rewrite <- PreH7.
    sepcon_assoc_change.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge DP_2 P_2 D_2)).
    Exists DT.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge CP_2 P_2 C_2)).
    Exists CT.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge AP_2 (P_2 * K) A_2)).
    Exists AT.
    sep_apply_l_atomic (uint_full_to_uchar_undef_full__array_bridges BP_2 P_2 B HP).
    sep_apply_l_atomic (uint_full_to_uchar_undef_full__array_bridges RP_2 K R HK).
    sep_apply_l_atomic (uint_full_to_uchar_undef_full__array_bridges
      NP_2 N_rational_feasibility_normal NB HN).
    repeat (progress cancel).
  - split_pures; dump_pre_spatial; try assumption.
    rewrite PreH5.
    eapply (sx_no_violated_filtered N_rational_feasibility_normal
      Rows_rational_feasibility_normal P_2 K D_2 C_2 A_2 B R);
      try assumption; lia.
Qed.

Lemma proof_of_sx_check_qcp_entail_wit_11_2 : sx_check_qcp_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH13 as Hdimensions.
  destruct Hdimensions as (HP & HN & _).
  assert (HK : 0 <= K) by lia.
  Exists A_2 C_2 D_2 NP_2 RP_2 BP_2 AP_2 CP_2 DP_2 K P_2.
  split_pure_spatial.
  - rewrite <- PreH12.
    sepcon_assoc_change.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge DP_2 P_2 D_2)).
    Exists DT.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge CP_2 P_2 C_2)).
    Exists CT.
    sep_apply_r_atomic (proj2 (scan_mpz_array_bridge AP_2 (P_2 * K) A_2)).
    Exists AT.
    sep_apply_l_atomic (uint_full_to_uchar_undef_full__array_bridges BP_2 P_2 B HP).
    sep_apply_l_atomic (uint_full_to_uchar_undef_full__array_bridges RP_2 K R HK).
    sep_apply_l_atomic (uint_full_to_uchar_undef_full__array_bridges
      NP_2 N_rational_feasibility_normal NB HN).
    repeat (progress cancel).
  - split_pures; dump_pre_spatial; try assumption.
    rewrite PreH10.
    eapply (sx_violated_blocked_filtered N_rational_feasibility_normal
      Rows_rational_feasibility_normal P_2 K D_2 C_2 A_2 B R retval);
      try assumption.
    exact (PreH4 PreH1).
Qed.

Lemma proof_of_sx_check_qcp_return_wit_2_split_goal_1 : sx_check_qcp_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  subst M_rational_feasibility_normal.
  pose proof (sx_positive_constant_infeasible N_rational_feasibility_normal
    Rows_rational_feasibility_normal i ltac:(lia) PreH14 PreH15) as Hinfeasible.
  unfold sx_check_result.
  split; [right; reflexivity |].
  split.
  - split; [discriminate | intros Hfeasible; contradiction].
  - split; [intros _; exact Hinfeasible | intros _; reflexivity].
Qed.

Lemma proof_of_sx_check_qcp_return_wit_2_split_goal_spatial : sx_check_qcp_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst next coef.
  pose proof (build_input_segment_app (sublist 0 (i + 1) Rows_rational_feasibility_normal)
    (sublist (i + 1) M_rational_feasibility_normal Rows_rational_feasibility_normal)
    head_pre (build_row_next (build_row_at Rows_rational_feasibility_normal i)) 0
    (N_rational_feasibility_normal + 1)) as Happend.
  rewrite <- (sublist_split 0 M_rational_feasibility_normal (i + 1)
    Rows_rational_feasibility_normal) in Happend by lia.
  rewrite (sublist_self Rows_rational_feasibility_normal M_rational_feasibility_normal) in Happend by lia.
  sep_apply_r_atomic Happend.
  cancel (build_input_segment (build_row_next (build_row_at Rows_rational_feasibility_normal i))
    0 (N_rational_feasibility_normal + 1)
    (sublist (i + 1) M_rational_feasibility_normal Rows_rational_feasibility_normal)).
  sep_apply_r_atomic (build_push_row__build_initial_table Rows_rational_feasibility_normal i
    head_pre q (N_rational_feasibility_normal + 1) ltac:(lia) ltac:(assumption) ltac:(assumption)).
  sepcon_assoc_change. cancel.
Qed.

Lemma proof_of_sx_check_qcp_return_wit_2 : sx_check_qcp_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_check_qcp_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_sx_check_qcp_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_1 : sx_check_qcp_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (simplex_dimensions_mpz_bytes P N_rational_feasibility_normal PreH10 PreH11) as Hbytes.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_2 : sx_check_qcp_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (simplex_dimensions_mpz_bytes P N_rational_feasibility_normal PreH10 PreH11) as Hbytes.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_3 : sx_check_qcp_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite sizeof_uint.
  pose proof (simplex_dimensions_bounds P N_rational_feasibility_normal PreH10) as Hbounds.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_4 : sx_check_qcp_partial_solve_wit_3_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite sizeof_uint.
  unfold simplex_dimensions_ok in PreH10.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_5 : sx_check_qcp_partial_solve_wit_3_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite sizeof_uint.
  unfold simplex_dimensions_ok in PreH10.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_6 : sx_check_qcp_partial_solve_wit_3_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (simplex_dimensions_mpz_bytes P N_rational_feasibility_normal PreH10 PreH11) as Hbytes.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_3_pure : sx_check_qcp_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_3.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_4.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_5.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_3_pure_split_goal_6.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_1 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (proj1 (valid_selection_first_aux N_rational_feasibility_normal K P
    D C A B R retval ltac:(lia) PreH12 PreH9 PreH11)) as Hrow.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_2 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite <- PreH15, <- PreH10.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_3 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (proj1 (valid_selection_first_aux N_rational_feasibility_normal K P
    D C A B R retval ltac:(lia) PreH12 PreH9 PreH11)) as Hrow.
  rewrite <- PreH15, <- PreH10.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_4 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (simplex_dimensions_mpz_bytes P N_rational_feasibility_normal PreH16 PreH17) as Hbytes.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_5 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (simplex_dimensions_mpz_bytes P N_rational_feasibility_normal PreH16 PreH17) as Hbytes.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_6 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite sizeof_uint.
  pose proof (simplex_dimensions_bounds P N_rational_feasibility_normal PreH16) as Hbounds.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_7 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite sizeof_uint.
  unfold simplex_dimensions_ok in PreH16.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_8 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (proj1 (valid_selection_first_aux N_rational_feasibility_normal K P
    D C A B R retval ltac:(lia) PreH12 PreH9 PreH11)) as Hrow.
  apply PreH17. lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_9 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  rewrite sizeof_uint.
  unfold simplex_dimensions_ok in PreH16.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_10 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (simplex_dimensions_mpz_bytes P N_rational_feasibility_normal PreH16 PreH17) as Hbytes.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_11 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (proj1 (valid_selection_first_aux N_rational_feasibility_normal K P
    D C A B R retval ltac:(lia) PreH12 PreH9 PreH11)) as Hrow.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_12 : sx_check_qcp_partial_solve_wit_4_pure_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial.
  pose proof (proj1 (valid_selection_first_aux N_rational_feasibility_normal K P
    D C A B R retval ltac:(lia) PreH12 PreH9 PreH11)) as Hrow.
  lia.
Qed.

Lemma proof_of_sx_check_qcp_partial_solve_wit_4_pure : sx_check_qcp_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_3.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_4.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_5.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_6.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_7.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_8.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_9.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_10.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_11.
  - Goal_apply proof_of_sx_check_qcp_partial_solve_wit_4_pure_split_goal_12.
Qed.

