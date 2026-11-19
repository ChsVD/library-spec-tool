From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_one_sided_policy_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import build_one_sided_policy_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.build_fme_model_input_revision_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_one_sided_policy_opt_lib.
Local Open Scope sac.

Lemma proof_of_build_one_sided_entail_wit_1_split_goal_1 : build_one_sided_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  pose proof (simplex_dimensions_bounds M N PreH3) as Hbounds.
  tauto.
Qed.

Lemma proof_of_build_one_sided_entail_wit_1_split_goal_2 : build_one_sided_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_dimensions_ok in PreH3.
  tauto.
Qed.

Lemma proof_of_build_one_sided_entail_wit_1 : build_one_sided_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_one_sided_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_build_one_sided_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_build_one_sided_entail_wit_2_split_goal_1 : build_one_sided_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  dump_pre_spatial.
  unfold os_masks_at, os_zeros.
  intros v Hv.
  assert (Hcolumn : (v <? 0)%Z = false) by (apply Z.ltb_ge; lia).
  rewrite Hcolumn, Zsublist_nil by lia.
  apply Znth_repeat.
Qed.

Lemma proof_of_build_one_sided_entail_wit_2_split_goal_2 : build_one_sided_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  dump_pre_spatial.
  rewrite PreH5.
  apply Zlength_nonneg.
Qed.

Lemma proof_of_build_one_sided_entail_wit_2_split_goal_spatial : build_one_sided_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  rewrite (Zsublist_nil Rows 0 0 ltac:(lia)), (sublist_self Rows M PreH5).
  cbn [build_input_segment].
  first [solve [cancel] | split_pure_spatial; [cancel | dump_pre_spatial; reflexivity]].
Qed.

Lemma proof_of_build_one_sided_entail_wit_2 : build_one_sided_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_one_sided_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_build_one_sided_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_build_one_sided_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_build_one_sided_entail_wit_3 : build_one_sided_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  prop_apply_p (build_tail_nonempty__build_initial_table
    q (N + 1) Rows rows M PreH12 ltac:(lia)).
  Intros_p Hlt.
  rewrite (build_suffix_cons__build_initial_table Rows rows M PreH2 ltac:(lia)) at 1.
  cbn [build_input_segment].
  Intros_p Hnode.
  destruct Hnode as [_ Hcoef].
  set (r := build_row_at Rows rows) in *.
  assert (Hinc : unsigned_last_nbits (rows + 1) 32 = rows + 1).
  {
    apply unsigned_last_nbits_eq.
    unfold simplex_dimensions_ok in PreH3.
    destruct PreH3 as (_ & Hn & Hsum & _).
    change (0 <= rows + 1 < UINT_MAX + 1).
    lia.
  }
  Exists Masks_2 (build_row_coefficients r) (build_row_next r) rows.
  split_pure_spatial.
  - fold r. sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_4 : build_one_sided_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (row := build_row_at Rows_stable_one_sided_build_normal i_2) in *.
  pose proof (MpzArray.full_split_to_missing_i coef_2 (j + 1)
    (N_stable_one_sided_build_normal + 1) (build_row_entries row) 0
    ltac:(lia)) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  sep_apply_l_atomic (os_mpz_size_open
    (coef_2 + (j + 1) * sizeof("__mpz_struct")) (os_coef row j)).
  Intros size.
  Exists size Masks_2 coef_2 next_2 i_2.
  fold row.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_build_one_sided_entail_wit_5_1 : build_one_sided_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (n := N_stable_one_sided_build_normal) in *.
  set (snapshot := Rows_stable_one_sided_build_normal) in *.
  set (updated :=
    replace_Znth j (Z.lor (unsigned_last_nbits (Znth j Masks_2 0) 8) 2) Masks_2) in *.
  prop_apply (UCharArray.full_Zlength signs n updated).
  Intros_p Hlength.
  unfold updated in Hlength.
  rewrite Zlength_replace_Znth in Hlength.
  pose proof (os_masks_step__sign_masks n i_2 j snapshot Masks_2 sz
    ltac:(lia) ltac:(lia) Hlength ltac:(assumption) ltac:(assumption)) as Hstep.
  assert (Hnegative : (Z.ltb sz 0) = true) by (apply Z.ltb_lt; lia).
  rewrite Hnegative in Hstep.
  pose proof (os_mpz_size_close (coef_2 + (j + 1) * mpz_sizeof)
    (os_coef (build_row_at snapshot i_2) j) sz) as Hclose.
  unfold mpz_sizeof in Hclose.
  sep_apply_l_atomic Hclose.
  pose proof (build_input_coefficients_restore coef_2 (j + 1) (n + 1)
    (build_row_entries (build_row_at snapshot i_2)) ltac:(lia)) as Hrestore.
  unfold mpz_sizeof in Hrestore.
  fold (os_coef (build_row_at snapshot i_2) j) in Hrestore.
  sep_apply_l_atomic Hrestore.
  Exists updated coef_2 next_2 i_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_5_2 : build_one_sided_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (n := N_stable_one_sided_build_normal) in *.
  set (snapshot := Rows_stable_one_sided_build_normal) in *.
  set (updated :=
    replace_Znth j (Z.lor (unsigned_last_nbits (Znth j Masks_2 0) 8) 1) Masks_2) in *.
  prop_apply (UCharArray.full_Zlength signs n updated).
  Intros_p Hlength.
  unfold updated in Hlength.
  rewrite Zlength_replace_Znth in Hlength.
  pose proof (os_masks_step__sign_masks n i_2 j snapshot Masks_2 sz
    ltac:(lia) ltac:(lia) Hlength ltac:(assumption) ltac:(assumption)) as Hstep.
  assert (Hnegative : (Z.ltb sz 0) = false) by (apply Z.ltb_ge; lia).
  assert (Hpositive : (Z.ltb 0 sz) = true) by (apply Z.ltb_lt; lia).
  rewrite Hnegative, Hpositive in Hstep.
  pose proof (os_mpz_size_close (coef_2 + (j + 1) * mpz_sizeof)
    (os_coef (build_row_at snapshot i_2) j) sz) as Hclose.
  unfold mpz_sizeof in Hclose.
  sep_apply_l_atomic Hclose.
  pose proof (build_input_coefficients_restore coef_2 (j + 1) (n + 1)
    (build_row_entries (build_row_at snapshot i_2)) ltac:(lia)) as Hrestore.
  unfold mpz_sizeof in Hrestore.
  fold (os_coef (build_row_at snapshot i_2) j) in Hrestore.
  sep_apply_l_atomic Hrestore.
  Exists updated coef_2 next_2 i_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_5_3 : build_one_sided_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (n := N_stable_one_sided_build_normal) in *.
  set (snapshot := Rows_stable_one_sided_build_normal) in *.
  set (updated :=
    Masks_2) in *.
  prop_apply (UCharArray.full_Zlength signs n updated).
  Intros_p Hlength.
  unfold updated in Hlength.
  pose proof (os_masks_step__sign_masks n i_2 j snapshot Masks_2 sz
    ltac:(lia) ltac:(lia) Hlength ltac:(assumption) ltac:(assumption)) as Hstep.
  assert (Hsize : sz = 0) by lia.
  rewrite Hsize in Hstep. cbn in Hstep.
  pose proof (os_mpz_size_close (coef_2 + (j + 1) * mpz_sizeof)
    (os_coef (build_row_at snapshot i_2) j) sz) as Hclose.
  unfold mpz_sizeof in Hclose.
  sep_apply_l_atomic Hclose.
  pose proof (build_input_coefficients_restore coef_2 (j + 1) (n + 1)
    (build_row_entries (build_row_at snapshot i_2)) ltac:(lia)) as Hrestore.
  unfold mpz_sizeof in Hrestore.
  fold (os_coef (build_row_at snapshot i_2) j) in Hrestore.
  sep_apply_l_atomic Hrestore.
  Exists updated coef_2 next_2 i_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_6_split_goal_1 : build_one_sided_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : os_masks_at ?n ?i j ?rows ?masks |- _ =>
      intros v Hv; specialize (H v Hv);
      assert (Hprocessed : (Z.ltb v j) = true) by (apply Z.ltb_lt; lia);
      assert (Hreset : (Z.ltb v 0) = false) by (apply Z.ltb_ge; lia);
      rewrite Hprocessed in H; now rewrite Hreset
  end.
Qed.

Lemma proof_of_build_one_sided_entail_wit_6_split_goal_spatial : build_one_sided_entail_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst rows coef next.
  cancel (simplex_malloc_token signs N_stable_one_sided_build_normal).
  cancel (build_input_segment (build_row_next (build_row_at Rows_stable_one_sided_build_normal i))
    0 (N_stable_one_sided_build_normal + 1)
    (sublist (i + 1) M_stable_one_sided_build_normal Rows_stable_one_sided_build_normal)).
  sep_apply_r_atomic (build_push_row__build_initial_table
    Rows_stable_one_sided_build_normal i head_pre q (N_stable_one_sided_build_normal + 1)
    ltac:(lia) ltac:(assumption) ltac:(assumption)).
  sepcon_assoc_change. cancel.
Qed.

Lemma proof_of_build_one_sided_entail_wit_6 : build_one_sided_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_one_sided_entail_wit_6_split_goal_spatial.
  - Goal_apply proof_of_build_one_sided_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_build_one_sided_entail_wit_7_split_goal_1 : build_one_sided_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  subst q.
  prop_apply_p (build_tail_null__build_initial_table
    (N + 1) Rows rows M PreH2 ltac:(lia)).
  Intros_p Hdone.
  dump_pre_spatial.
  now subst rows.
Qed.

Lemma proof_of_build_one_sided_entail_wit_7_split_goal_2 : build_one_sided_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  dump_pre_spatial.
  destruct (Z.eq_dec M 0) as [-> | Hnonzero].
  - cbn. lia.
  - destruct (PreH5 ltac:(lia)) as [Hsize _].
    rewrite Hsize.
    pose proof (simplex_dimensions_bounds M N PreH3) as Hbounds.
    lia.
Qed.

Lemma proof_of_build_one_sided_entail_wit_7_split_goal_3 : build_one_sided_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  subst q.
  prop_apply_p (build_tail_null__build_initial_table
    (N + 1) Rows rows M PreH2 ltac:(lia)).
  Intros_p Hdone.
  dump_pre_spatial.
  exact Hdone.
Qed.

Lemma proof_of_build_one_sided_entail_wit_7_split_goal_spatial : build_one_sided_entail_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  subst q.
  sep_apply (build_input_segment_app (sublist 0 rows Rows)
    (sublist rows M Rows) head_pre 0 0 (N + 1)).
  rewrite <- (sublist_split 0 M rows Rows) by lia.
  rewrite (sublist_self Rows M PreH2).
  cancel.
Qed.

Lemma proof_of_build_one_sided_entail_wit_7 : build_one_sided_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_one_sided_entail_wit_7_split_goal_spatial.
  - Goal_apply proof_of_build_one_sided_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_build_one_sided_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_build_one_sided_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_build_one_sided_entail_wit_8 : build_one_sided_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  assert (HMnonneg : 0 <= M) by (unfold simplex_dimensions_ok in PreH6; tauto).
  assert (Halloc : 0 < M ->
      (0 < retval /\ retval = 4 * align4) /\
      retval + (M + -1) * sizeof("InequList") <= UINT_MAX).
  {
    intro HM.
    destruct (PreH8 HM) as [Hsize _].
    rewrite Hsize in PreH3 |- *.
    destruct (PreH3 ltac:(lia)) as [Hpositive Hlast].
    split; [exact Hpositive | lia].
  }
  Exists Masks_2 align4 0.
  unfold os_kept_prefix.
  rewrite (Zsublist_nil Rows 0 0 ltac:(lia)), (sublist_self Rows M PreH5).
  cbn [List.filter os_shadows os_temp_head os_links build_input_segment Z.mul].
  sep_apply (UCharArray.undef_full_to_undef_seg retval (M * sizeof("InequList"))).
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia |
             intros HM; destruct (Halloc HM) as [Hbase Hlast]; assumption].
Qed.

Lemma proof_of_build_one_sided_entail_wit_9 : build_one_sided_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  prop_apply_p (build_tail_nonempty__build_initial_table
    q (N + 1) Rows i_2 M PreH19 ltac:(lia)).
  Intros_p Hlt.
  rewrite (build_suffix_cons__build_initial_table Rows i_2 M PreH2 ltac:(lia)) at 1.
  cbn [build_input_segment].
  Intros_p Hnode.
  destruct Hnode as [_ Hcoef].
  set (r := build_row_at Rows i_2) in *.
  Exists (build_row_coefficients r) (build_row_next r) NodesAlign_2 Masks_2 i_2.
  split_pure_spatial.
  - fold r. sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | unfold os_checked_prefix; intros; lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_10 : build_one_sided_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (row := build_row_at Rows_stable_one_sided_build_normal i_2) in *.
  pose proof (MpzArray.full_split_to_missing_i coef_2 (j + 1)
    (N_stable_one_sided_build_normal + 1) (build_row_entries row) 0
    ltac:(lia)) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  sep_apply_l_atomic (os_mpz_size_open
    (coef_2 + (j + 1) * sizeof("__mpz_struct")) (os_coef row j)).
  Intros size.
  Exists size coef_2 next_2 NodesAlign_2 Masks_2 i_2.
  fold row.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_build_one_sided_entail_wit_11_1 : build_one_sided_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  Exists coef_2 next_2 NodesAlign_2 Masks_2 i_2.
  split_pure_spatial.
  - change (sizeof("__mpz_struct")) with mpz_sizeof.
    sep_apply (os_mpz_size_close (coef_2 + (j + 1) * mpz_sizeof)
      (os_coef (build_row_at Rows i_2) j) sz).
    unfold os_coef at 1.
    sep_apply (build_input_coefficients_restore coef_2 (j + 1) (N + 1)
      (build_row_entries (build_row_at Rows i_2)) ltac:(lia)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | lia].
    intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hkj].
    + apply os_keep_col_bit.
      left.
      assert (Hmask : Znth j Masks_2 0 = os_mask j Rows).
      {
        pose proof (PreH5 j ltac:(lia)) as Hjmask.
        assert (Hnonneg : (j <? 0)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite Hnonneg, (sublist_self _ _ PreH7) in Hjmask.
        exact Hjmask.
      }
      rewrite <- Hmask. split; assumption.
    + match goal with
      | H : os_checked_prefix Rows (build_row_at Rows i_2) j |- _ =>
          apply H; lia
      end.
Qed.

Lemma proof_of_build_one_sided_entail_wit_11_2 : build_one_sided_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  Exists coef_2 next_2 NodesAlign_2 Masks_2 i_2.
  split_pure_spatial.
  - change (sizeof("__mpz_struct")) with mpz_sizeof.
    sep_apply (os_mpz_size_close (coef_2 + (j + 1) * mpz_sizeof)
      (os_coef (build_row_at Rows i_2) j) sz).
    unfold os_coef at 1.
    sep_apply (build_input_coefficients_restore coef_2 (j + 1) (N + 1)
      (build_row_entries (build_row_at Rows i_2)) ltac:(lia)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | lia].
    intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hkj].
    + apply os_keep_col_bit.
      right.
      unfold os_size_relation in PreH28.
      rewrite PreH1 in PreH28.
      apply Z.sgn_null_iff.
      symmetry. exact PreH28.
    + match goal with
      | H : os_checked_prefix Rows (build_row_at Rows i_2) j |- _ =>
          apply H; lia
      end.
Qed.

Lemma proof_of_build_one_sided_entail_wit_11_3 : build_one_sided_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  Exists coef_2 next_2 NodesAlign_2 Masks_2 i_2.
  split_pure_spatial.
  - change (sizeof("__mpz_struct")) with mpz_sizeof.
    sep_apply (os_mpz_size_close (coef_2 + (j + 1) * mpz_sizeof)
      (os_coef (build_row_at Rows i_2) j) sz).
    unfold os_coef at 1.
    sep_apply (build_input_coefficients_restore coef_2 (j + 1) (N + 1)
      (build_row_entries (build_row_at Rows i_2)) ltac:(lia)).
    cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try solve [assumption | lia].
    intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hkj].
    + apply os_keep_col_bit.
      right.
      unfold os_size_relation in PreH29.
      rewrite PreH1 in PreH29.
      apply Z.sgn_null_iff.
      symmetry. exact PreH29.
    + match goal with
      | H : os_checked_prefix Rows (build_row_at Rows i_2) j |- _ =>
          apply H; lia
      end.
Qed.

Lemma proof_of_build_one_sided_entail_wit_12 : build_one_sided_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into rows,
         M_stable_one_sided_build_normal into m,
         N_stable_one_sided_build_normal into n.
  subst j.
  assert (Hlayout : os_node_layout) by (apply PreH10; lia).
  destruct (PreH14 ltac:(lia)) as [Hnodes Halign].
  assert (Hdiv : (4 | nodes)) by (exists NodesAlign_2; lia).
  sep_apply (os_open_packed_slot__packed_nodes nodes kept m Hlayout
    ltac:(lia) ltac:(lia) Hdiv).
  assert (Hlen : kept = Zlength (os_kept_prefix n i_2 rows)) by assumption.
  destruct (Z.eq_dec kept 0) as [Hzero|Hnonzero].
  - assert (Hempty : os_kept_prefix n i_2 rows = nil).
    { apply os_empty_if_length_zero__packed_nodes. lia. }
    rewrite Hempty. unfold os_temp_head. rewrite Hzero.
    cbn [Z.eqb os_shadows os_links].
    Intros_p Hnull.
    Left. Exists coef_2 next_2 NodesAlign_2 Masks_2 i_2.
    split_pure_spatial.
    + sepcon_assoc_change. cancel.
    + split_pures; dump_pre_spatial; solve [assumption | lia].
  - assert (Hhead : os_temp_head nodes kept = nodes).
    { unfold os_temp_head. apply Z.eqb_neq in Hnonzero. now rewrite Hnonzero. }
    rewrite Hhead.
    pose proof (os_links_last_split__packed_nodes nodes 0 (os_kept_prefix n i_2 rows)
      ltac:(lia)) as Hsplit.
    rewrite <- Hlen, Z.add_0_l, Z.mul_0_l, Z.add_0_r in Hsplit.
    sep_apply Hsplit.
    Right. Exists coef_2 next_2 NodesAlign_2 Masks_2 i_2.
    split_pure_spatial.
    + sepcon_assoc_change. cancel.
    + split_pures; dump_pre_spatial; solve [assumption | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_13_1 : build_one_sided_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into rows,
         M_stable_one_sided_build_normal into m,
         N_stable_one_sided_build_normal into n.
  assert (Hi : 0 <= i_2 < Zlength rows) by lia.
  assert (Hlen : kept = Zlength (os_kept_prefix n i_2 rows)) by assumption.
  assert (Haccept : forallb (os_keep_col rows (build_row_at rows i_2)) (ZRange.Zrange 0 n) = true).
  { apply os_filter_accept__packed_nodes. assumption. }
  pose proof (os_kept_prefix_step__packed_nodes n i_2 rows Hi) as Hstep.
  cbn [filter] in Hstep. rewrite Haccept in Hstep.
  assert (Hhead : os_temp_head nodes (kept+1) = nodes).
  { unfold os_temp_head. destruct ((kept + 1 =? 0)%Z) eqn:Heq; [apply Z.eqb_eq in Heq; lia|reflexivity]. }
  assert (Hq : q <> 0) by assumption.
  assert (Hcoef_eq : coef = build_row_coefficients (build_row_at rows i_2)) by assumption.
  assert (Hcoef : build_row_coefficients (build_row_at rows i_2) <> 0) by lia.
  assert (Hnext_eq : next = build_row_next (build_row_at rows i_2)) by assumption.
  rewrite Hcoef_eq, Hnext_eq.
  assert (Hnodes : 0 < nodes) by (apply (proj1 (PreH13 ltac:(lia)))).
  assert (Hstride : sizeof("InequList") = 8) by (apply (proj1 (PreH9 ltac:(lia)))).
  Exists Masks_2 NodesAlign_2 (i_2 + 1).
  rewrite Hstep, Hhead.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
    sep_apply_r_atomic (build_push_row__build_initial_table rows i_2 head_pre q (n+1) Hi Hq Hcoef).
    rewrite (os_shadows_snoc__packed_nodes nodes 0 (os_kept_prefix n i_2 rows)
      (build_row_at rows i_2) ltac:(lia)), <- Hlen, Z.add_0_l.
    lazymatch goal with
    | |- context [os_links nodes 0 (List.app ?prefix ?suffix)] =>
        sep_apply_r_atomic (os_links_append__packed_nodes nodes
          (nodes+(kept-1)*sizeof("InequList")) 0 prefix suffix)
    end.
    cbn [os_links build_row_coefficients build_row_next].
    asrt_simpl.
    split_pure_spatial; [sepcon_assoc_change; cancel|].
    split_pures; dump_pre_spatial; try rewrite Hstride; lia.
  - split_pures; dump_pre_spatial; try solve [assumption | lia].
    rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_build_one_sided_entail_wit_13_2 : build_one_sided_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into rows,
         M_stable_one_sided_build_normal into m,
         N_stable_one_sided_build_normal into n.
  assert (Hi : 0 <= i_2 < Zlength rows) by lia.
  assert (Hlen : kept = Zlength (os_kept_prefix n i_2 rows)) by assumption.
  assert (Haccept : forallb (os_keep_col rows (build_row_at rows i_2)) (ZRange.Zrange 0 n) = true).
  { apply os_filter_accept__packed_nodes. assumption. }
  pose proof (os_kept_prefix_step__packed_nodes n i_2 rows Hi) as Hstep.
  cbn [filter] in Hstep. rewrite Haccept in Hstep.
  assert (Hhead : os_temp_head nodes (kept+1) = nodes).
  { unfold os_temp_head. destruct ((kept + 1 =? 0)%Z) eqn:Heq; [apply Z.eqb_eq in Heq; lia|reflexivity]. }
  assert (Hq : q <> 0) by assumption.
  assert (Hcoef_eq : coef = build_row_coefficients (build_row_at rows i_2)) by assumption.
  assert (Hcoef : build_row_coefficients (build_row_at rows i_2) <> 0) by lia.
  assert (Hnext_eq : next = build_row_next (build_row_at rows i_2)) by assumption.
  rewrite Hcoef_eq, Hnext_eq.
  assert (Hnodes : 0 < nodes) by (apply (proj1 (PreH13 ltac:(lia)))).
  Exists Masks_2 NodesAlign_2 (i_2 + 1).
  rewrite Hstep, Hhead.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
    sep_apply_r_atomic (build_push_row__build_initial_table rows i_2 head_pre q (n+1) Hi Hq Hcoef).
    assert (Hempty : os_kept_prefix n i_2 rows = nil).
    { apply os_empty_if_length_zero__packed_nodes. lia. }
    rewrite Hempty.
    assert (Hzero : kept = 0) by assumption.
    rewrite Hzero, Z.mul_0_l, Z.add_0_r.
    cbn [app os_shadows os_links build_row_coefficients build_row_next].
    asrt_simpl.
    split_pure_spatial; [sepcon_assoc_change; cancel|].
    split_pures; dump_pre_spatial; lia.
  - split_pures; dump_pre_spatial; try solve [assumption | lia].
    rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_build_one_sided_entail_wit_13_3 : build_one_sided_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into rows,
         M_stable_one_sided_build_normal into m,
         N_stable_one_sided_build_normal into n.
  assert (Hi : 0 <= i_2 < Zlength rows) by lia.
  assert (Hj : 0 <= j < n) by lia.
  assert (Hreject : forallb (os_keep_col rows (build_row_at rows i_2)) (ZRange.Zrange 0 n) = false).
  { apply (os_filter_reject__packed_nodes n m rows Masks_2 (build_row_at rows i_2) j sz);
      solve [assumption | lia]. }
  pose proof (os_kept_prefix_step__packed_nodes n i_2 rows Hi) as Hstep.
  cbn [filter] in Hstep. rewrite Hreject, app_nil_r in Hstep.
  Exists Masks_2 NodesAlign_2 (i_2 + 1).
  rewrite Hstep.
  split_pure_spatial.
  - assert (Hq : q <> 0) by assumption.
    assert (Hcoef : build_row_coefficients (build_row_at rows i_2) <> 0) by lia.
    assert (Hcoef_eq : coef = build_row_coefficients (build_row_at rows i_2)) by assumption.
    assert (Hnext_eq : next = build_row_next (build_row_at rows i_2)) by assumption.
    rewrite Hcoef_eq, Hnext_eq.
    sepcon_assoc_change. cancel.
    sep_apply_r_atomic (build_push_row__build_initial_table rows i_2 head_pre q (n+1) Hi Hq Hcoef).
    sep_apply_r_atomic (build_input_coefficients_restore
      (build_row_coefficients (build_row_at rows i_2)) (j + 1) (n + 1)
      (build_row_entries (build_row_at rows i_2)) ltac:(lia)).
    unfold os_coef.
    pose proof (os_mpz_size_close
      (build_row_coefficients (build_row_at rows i_2) + (j + 1) * mpz_sizeof)
      (Znth (j + 1) (build_row_entries (build_row_at rows i_2)) 0) sz) as Hclose.
    unfold mpz_sizeof in Hclose |- *.
    sepcon_assoc_change.
    first [sep_apply_r_atomic Hclose | sep_apply_l_atomic Hclose].
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; solve [assumption | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_13_4 : build_one_sided_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into rows,
         M_stable_one_sided_build_normal into m,
         N_stable_one_sided_build_normal into n.
  assert (Hi : 0 <= i_2 < Zlength rows) by lia.
  assert (Hj : 0 <= j < n) by lia.
  assert (Hreject : forallb (os_keep_col rows (build_row_at rows i_2)) (ZRange.Zrange 0 n) = false).
  { apply (os_filter_reject__packed_nodes n m rows Masks_2 (build_row_at rows i_2) j sz);
      solve [assumption | lia]. }
  pose proof (os_kept_prefix_step__packed_nodes n i_2 rows Hi) as Hstep.
  cbn [filter] in Hstep. rewrite Hreject, app_nil_r in Hstep.
  Exists Masks_2 NodesAlign_2 (i_2 + 1).
  rewrite Hstep.
  split_pure_spatial.
  - assert (Hq : q <> 0) by assumption.
    assert (Hcoef : build_row_coefficients (build_row_at rows i_2) <> 0) by lia.
    assert (Hcoef_eq : coef = build_row_coefficients (build_row_at rows i_2)) by assumption.
    assert (Hnext_eq : next = build_row_next (build_row_at rows i_2)) by assumption.
    rewrite Hcoef_eq, Hnext_eq.
    sepcon_assoc_change. cancel.
    sep_apply_r_atomic (build_push_row__build_initial_table rows i_2 head_pre q (n+1) Hi Hq Hcoef).
    sep_apply_r_atomic (build_input_coefficients_restore
      (build_row_coefficients (build_row_at rows i_2)) (j + 1) (n + 1)
      (build_row_entries (build_row_at rows i_2)) ltac:(lia)).
    unfold os_coef.
    pose proof (os_mpz_size_close
      (build_row_coefficients (build_row_at rows i_2) + (j + 1) * mpz_sizeof)
      (Znth (j + 1) (build_row_entries (build_row_at rows i_2)) 0) sz) as Hclose.
    unfold mpz_sizeof in Hclose |- *.
    sepcon_assoc_change.
    first [sep_apply_r_atomic Hclose | sep_apply_l_atomic Hclose].
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; solve [assumption | lia].
Qed.

Lemma proof_of_build_one_sided_entail_wit_14 : build_one_sided_entail_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  assert (Hdim : simplex_dimensions_ok kept N).
  { eapply simplex_dimensions_smaller; [eassumption | lia]. }
  assert (Hlayout : 0 < kept -> simplex_mpz_layout).
  { intros. apply PreH4. lia. }
  subst q.
  prop_apply_p (build_tail_null__build_initial_table (N + 1) Rows i M
    PreH2 ltac:(lia)).
  Intros_p Hend.
  subst i.
  unfold os_kept_prefix in *.
  rewrite (sublist_self _ _ PreH2) in *.
  rewrite Zsublist_nil by lia.
  cbn [build_input_segment].
  Intros_p Hempty.
  sep_apply (proj1 (os_transfer
    (fun r => forallb (os_keep_col Rows r) (SumLib.ZRange.Zrange 0 N))
    nodes 0 head_pre (os_temp_head nodes kept) (N + 1) Rows)).
  fold (os_unborrowed_kept N head_pre Rows).
  fold (os_kept N Rows).
  destruct (Z.eq_dec kept 0) as [Hzero | Hpositive].
  - Left. Exists Masks_2.
    split_pure_spatial.
    + unfold os_temp_head. rewrite (proj2 (Z.eqb_eq kept 0) Hzero). sepcon_assoc_change; cancel; reflexivity.
    + split_pures; dump_pre_spatial; (assumption || lia).
  - Right. Exists Masks_2.
    split_pure_spatial.
    + unfold os_temp_head. rewrite (proj2 (Z.eqb_neq kept 0) Hpositive). sepcon_assoc_change; cancel; reflexivity.
    + split_pures; dump_pre_spatial; (assumption || lia).
Qed.

Lemma proof_of_build_one_sided_entail_wit_15_1 : build_one_sided_entail_wit_15_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  subst variables_pre.
  rewrite !os_shadows_length, !os_shadows_matrix in PreH2, PreH3.
  rewrite os_shadows_length in PreH4.
  rewrite <- PreH14 in PreH2, PreH3, PreH4.
  rewrite !os_shadows_length, <- PreH14.
  subst retval_cols.
  Exists nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 (kept + N) kept
    dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 nbVals_2.
  split_pure_spatial.
  - pose proof (os_recover_input__build_transfer N M kept head_pre nodes Rows
      PreH14 PreH16 PreH10) as Hrecover.
    unfold os_temp_head in Hrecover.
    rewrite (proj2 (Z.eqb_neq kept 0) PreH5) in Hrecover.
    sep_apply Hrecover.
    sep_apply (UCharArray.full_to_undef_full signs N Masks).
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_build_one_sided_entail_wit_15_2 : build_one_sided_entail_wit_15_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename Rows_stable_one_sided_build_normal into Rows.
  rename M_stable_one_sided_build_normal into M.
  rename N_stable_one_sided_build_normal into N.
  subst variables_pre.
  rewrite !os_shadows_length, !os_shadows_matrix in PreH2, PreH3.
  rewrite os_shadows_length in PreH4.
  rewrite <- PreH14 in PreH2, PreH3, PreH4.
  rewrite !os_shadows_length, <- PreH14.
  subst retval_cols.
  Exists nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2 (kept + N) kept
    dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 nbVals_2.
  split_pure_spatial.
  - pose proof (os_recover_input__build_transfer N M kept head_pre nodes Rows
      PreH14 PreH16 PreH10) as Hrecover.
    unfold os_temp_head in Hrecover.
    rewrite (proj2 (Z.eqb_eq kept 0) PreH5) in Hrecover.
    sep_apply Hrecover.
    sep_apply (UCharArray.full_to_undef_full signs N Masks).
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_build_one_sided_return_wit_1 : build_one_sided_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists nbPtr_2 rowPtr_2 bPtr_2 aPtr_2 cPtr_2 dPtr_2
    t_addr_cols t_addr_rows dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 nbVals_2.
  rewrite PreH4, PreH5, <- PreH6.
  split_pure_spatial.
  - sepcon_right_assoc.
    cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity].
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_1 : build_one_sided_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite os_shadows_length, <- PreH16.
  assumption.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_2 : build_one_sided_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite os_shadows_length, <- PreH16.
  assumption.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_3 : build_one_sided_partial_solve_wit_9_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite os_shadows_length, <- PreH16.
  assumption.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_4 : build_one_sided_partial_solve_wit_9_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite os_shadows_length, <- PreH16.
  assumption.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_9_pure : build_one_sided_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_2.
  - Goal_apply proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_3.
  - Goal_apply proof_of_build_one_sided_partial_solve_wit_9_pure_split_goal_4.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_10_pure_split_goal_1 : build_one_sided_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite os_shadows_length, <- PreH16.
  assumption.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_10_pure_split_goal_2 : build_one_sided_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite os_shadows_length, <- PreH16.
  assumption.
Qed.

Lemma proof_of_build_one_sided_partial_solve_wit_10_pure : build_one_sided_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_one_sided_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_build_one_sided_partial_solve_wit_10_pure_split_goal_2.
Qed.

