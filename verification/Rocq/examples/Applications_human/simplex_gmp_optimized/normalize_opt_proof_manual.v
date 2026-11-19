From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import normalize_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import normalize_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.normalize_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib.
Local Open Scope sac.

Lemma proof_of_normalize_entail_wit_1_split_goal_spatial : normalize_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  sep_apply_l_atomic (MpzArray.full_split_to_missing_i
    DP_normalize_staged_row I_normalize_staged_row M_normalize_staged_row D_normalize_staged_row 0 ltac:(lia)).
  unfold mpz_store, mpz_sizeof.
  cancel.
Qed.

Lemma proof_of_normalize_entail_wit_1 : normalize_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_normalize_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_normalize_entail_wit_2 : normalize_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct PreH1 as (Hrows & Hcols & Htotal & Hbytes & Hindices).
  assert (Hdim : simplex_dimensions_ok M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row))
    by (repeat split; assumption).
  Exists 0 0 (Znth I_normalize_staged_row D_normalize_staged_row 0).
  change (store_Z (DP_normalize_staged_row + (I_normalize_staged_row) * sizeof("__mpz_struct")) (Znth I_normalize_staged_row D_normalize_staged_row 0))
    with (mpz_store DP_normalize_staged_row (I_normalize_staged_row) (Znth I_normalize_staged_row D_normalize_staged_row 0)).
  sep_apply_l_atomic (MpzArray.missing_i_merge_to_full
    DP_normalize_staged_row (I_normalize_staged_row) (M_normalize_staged_row) (Znth I_normalize_staged_row D_normalize_staged_row 0) D_normalize_staged_row ltac:(lia)).
  rewrite replace_Znth_Znth.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try rewrite normalize_prefix_gcd_empty; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_3_1 : normalize_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z at 1.
  Intros gd gs gcap.
  destruct (Z.eq_dec gs 1) as [-> | Hsize].
  - rewrite (Z.abs_eq G_2) by lia.
    change (Z.abs 1) with 1.
    sep_apply_l_atomic (normalize_single_limb_open gd G_2).
    Intros_p Hlimb.
    Left.
    Exists Rem_2 T_2 gd gcap 1 G_2.
    rewrite ?eval_addr.
    change (Zabs 1) with 1 in *.
    split_pure_spatial.
    + cancel (UIntArray.full gd 1 (G_2 :: nil)).
      cancel.
    + split_pures; dump_pre_spatial; try assumption;
        unfold UINT_MOD in Hlimb; lia.
  - Right.
    Exists Rem_2 T_2 gd gcap gs G_2.
    rewrite ?eval_addr.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD gd (Zabs G_2) (Zabs gs)).
      cancel.
    + split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_3_2 : normalize_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hslot : 0 <= slot < Zlength N_normalize_staged_row) by lia.
  destruct (normalize_slot_range K_normalize_staged_row B_normalize_staged_row
    R_normalize_staged_row N_normalize_staged_row slot PreH7 Hslot) as [[Hlo Hhi] Hcolumn].
  unfold store_Z at 1.
  Intros gd gs gcap.
  destruct (Z.eq_dec gs 1) as [-> | Hsize].
  - rewrite (Z.abs_eq G_2) by lia.
    change (Z.abs 1) with 1.
    sep_apply_l_atomic (normalize_single_limb_open gd G_2).
    Intros_p Hlimb.
    Left.
    Exists Rem_2 T_2 gd gcap 1 (Znth slot N_normalize_staged_row 0) G_2.
    rewrite ?eval_addr.
    change (Zabs 1) with 1 in *.
    split_pure_spatial.
    + cancel (UIntArray.full gd 1 (G_2 :: nil)).
      cancel.
    + split_pures; dump_pre_spatial; try assumption;
        unfold UINT_MOD in Hlimb; lia.
  - Right.
    Exists Rem_2 T_2 gd gcap gs (Znth slot N_normalize_staged_row 0) G_2.
    rewrite ?eval_addr.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD gd (Zabs G_2) (Zabs gs)).
      cancel.
    + split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_4_1 : normalize_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename CP_normalize_staged_row into cp.
  rename C_normalize_staged_row into constants.
  rename I_normalize_staged_row into row_index.
  rename M_normalize_staged_row into rows.
  pose proof (store_Z_from_fields (&("g")) gd gs gcap G_2 PreH20 PreH19) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "g")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  pose proof (MpzArray.full_split_to_missing_i cp row_index rows constants 0
    ltac:(lia)) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists Rem_2 T_2 (Znth row_index constants 0) G_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_normalize_entail_wit_4_2 : normalize_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename CP_normalize_staged_row into cp.
  rename C_normalize_staged_row into constants.
  rename I_normalize_staged_row into row_index.
  rename M_normalize_staged_row into rows.
  replace (replace_Znth 0 G_2 (G_2 :: nil)) with (G_2 :: nil) by reflexivity.
  assert (Hlimb : 1 <= G_2 < UINT_MOD) by (unfold UINT_MOD; lia).
  pose proof (normalize_single_limb_close gd G_2 Hlimb) as Hcompact.
  assert (HGabs : Zabs G_2 = G_2) by (apply Z.abs_eq; lia).
  assert (Hsizeabs : Zabs gs = 1) by (rewrite PreH22; reflexivity).
  replace (mpd_store_Z_compact UINT_MOD gd G_2 1)
    with (mpd_store_Z_compact UINT_MOD gd (Zabs G_2) (Zabs gs)) in Hcompact
    by now rewrite HGabs, Hsizeabs.
  sep_apply_l_atomic Hcompact.
  pose proof (store_Z_from_fields (&("g")) gd gs gcap G_2 PreH21 PreH20) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "g")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  pose proof (MpzArray.full_split_to_missing_i cp row_index rows constants 0
    ltac:(lia)) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists Rem_2 T_2 (Znth row_index constants 0) G_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_normalize_entail_wit_4_3 : normalize_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename AP_normalize_staged_row into ap.
  rename A_normalize_staged_row into coefficients.
  rename I_normalize_staged_row into row_index.
  rename M_normalize_staged_row into rows.
  rename K_normalize_staged_row into cols.
  rename R_normalize_staged_row into row_map.
  rename N_normalize_staged_row into nonbasic.
  rename B_normalize_staged_row into basic.
  assert (Hslot : 0 <= slot < Zlength nonbasic) by lia.
  pose proof (normalize_slot_range cols basic row_map nonbasic slot PreH9 Hslot)
    as [Hcolumn Hnonbasic].
  rewrite <- PreH22 in Hcolumn, Hnonbasic.
  pose proof (simplex_dimensions_index rows (cols - rows) row_index j PreH5
    ltac:(lia) ltac:(lia)) as Hindex.
  pose proof (proj1 (simplex_dimensions_bounds rows (cols - rows) PreH5)) as Htotal.
  replace (rows + (cols - rows)) with cols in Hindex, Htotal by lia.
  assert (Hoffset : unsigned_last_nbits (row_index * cols) 32 = row_index * cols).
  { apply unsigned_last_nbits_eq.
    assert (Hnonnegative : 0 <= row_index * cols) by (apply Z.mul_nonneg_nonneg; lia).
    change (0 <= row_index * cols < 4294967296).
    change (0 <= rows * cols <= 2147483647) in Htotal.
    lia. }
  rewrite Hoffset.
  pose proof (store_Z_from_fields (&("g")) gd gs gcap G_2 PreH27 PreH26) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "g")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  pose proof (MpzArray.full_split_to_missing_i ap (row_index * cols + j) (rows * cols) coefficients 0
    Hindex) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists Rem_2 T_2 (Znth (row_index * cols + j) coefficients 0) j G_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_normalize_entail_wit_4_4 : normalize_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename AP_normalize_staged_row into ap.
  rename A_normalize_staged_row into coefficients.
  rename I_normalize_staged_row into row_index.
  rename M_normalize_staged_row into rows.
  rename K_normalize_staged_row into cols.
  rename R_normalize_staged_row into row_map.
  rename N_normalize_staged_row into nonbasic.
  rename B_normalize_staged_row into basic.
  assert (Hslot : 0 <= slot < Zlength nonbasic) by lia.
  pose proof (normalize_slot_range cols basic row_map nonbasic slot PreH10 Hslot)
    as [Hcolumn Hnonbasic].
  rewrite <- PreH23 in Hcolumn, Hnonbasic.
  pose proof (simplex_dimensions_index rows (cols - rows) row_index j PreH6
    ltac:(lia) ltac:(lia)) as Hindex.
  pose proof (proj1 (simplex_dimensions_bounds rows (cols - rows) PreH6)) as Htotal.
  replace (rows + (cols - rows)) with cols in Hindex, Htotal by lia.
  assert (Hoffset : unsigned_last_nbits (row_index * cols) 32 = row_index * cols).
  { apply unsigned_last_nbits_eq.
    assert (Hnonnegative : 0 <= row_index * cols) by (apply Z.mul_nonneg_nonneg; lia).
    change (0 <= row_index * cols < 4294967296).
    change (0 <= rows * cols <= 2147483647) in Htotal.
    lia. }
  rewrite Hoffset.
  replace (replace_Znth 0 G_2 (G_2 :: nil)) with (G_2 :: nil) by reflexivity.
  assert (Hlimb : 1 <= G_2 < UINT_MOD) by (unfold UINT_MOD; lia).
  pose proof (normalize_single_limb_close gd G_2 Hlimb) as Hcompact.
  assert (HGabs : Zabs G_2 = G_2) by (apply Z.abs_eq; lia).
  assert (Hsizeabs : Zabs gs = 1) by (rewrite PreH29; reflexivity).
  replace (mpd_store_Z_compact UINT_MOD gd G_2 1)
    with (mpd_store_Z_compact UINT_MOD gd (Zabs G_2) (Zabs gs)) in Hcompact
    by now rewrite HGabs, Hsizeabs.
  sep_apply_l_atomic Hcompact.
  pose proof (store_Z_from_fields (&("g")) gd gs gcap G_2 PreH28 PreH27) as Hfields.
  rewrite (eval_addr (RE_addr_of (LE_var "g")) (FET_alias "__mpz_struct")) in Hfields.
  sep_apply_l_atomic Hfields.
  pose proof (MpzArray.full_split_to_missing_i ap (row_index * cols + j) (rows * cols) coefficients 0
    Hindex) as Hsplit.
  unfold mpz_store, mpz_sizeof in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists Rem_2 T_2 (Znth (row_index * cols + j) coefficients 0) j G_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_normalize_entail_wit_5_1 : normalize_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_normalize_staged_row into A,
    C_normalize_staged_row into C,
    D_normalize_staged_row into D,
    N_normalize_staged_row into N,
    I_normalize_staged_row into I,
    K_normalize_staged_row into K,
    M_normalize_staged_row into M,
    AP_normalize_staged_row into AP.
  subst j.
  set (values := normalize_row_values K I A C N) in *.
  set (g := normalize_prefix_gcd (Znth I D 0) slot values) in *.
  assert (Hg : 0 < g) by lia.
  set (column := Znth slot N 0) in *.
  pose proof (simplex_dimensions_index M (K - M) I column
    PreH7 ltac:(lia) ltac:(lia)) as Hindex.
  replace (M + (K - M)) with K in Hindex by lia.
  set (operand := Znth (I * K + column) A 0) in *.
  set (rem := Z.rem operand g) in *.
  assert (Hscan :
    Znth slot values 0 = operand).
  { unfold values, operand, column.
    apply normalize_row_values_column. lia. }
  assert (Hstep :
    normalize_prefix_gcd (Znth I D 0) (slot + 1) values = Z.gcd g operand).
  { rewrite normalize_prefix_gcd_step.
    - now rewrite Hscan.
    - unfold values. rewrite normalize_row_values_length. lia. }
  set (next := Z.gcd g rem) in *.
  assert (Hnext : normalize_prefix_gcd (Znth I D 0) (slot + 1) values = next).
  { rewrite Hstep. unfold next, rem. symmetry. exact (normalize_rem_gcd g operand Hg). }
  assert (Hpositive : 0 < next).
  { rewrite <- Hnext. apply normalize_fold_gcd_positive. exact PreH12. }
  subst x.
  change (store_Z (AP + (I * K + column) * sizeof ("__mpz_struct")) operand)
    with (mpz_store AP (I * K + column) operand).
  sep_apply_l_atomic
    (MpzArray.missing_i_merge_to_full AP (I * K + column) (M * K) operand A Hindex).
  unfold operand.
  rewrite replace_Znth_Znth.
  Exists rem next next.
  split_pure_spatial.
  - sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_normalize_entail_wit_5_2 : normalize_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_normalize_staged_row into A,
    C_normalize_staged_row into C,
    D_normalize_staged_row into D,
    N_normalize_staged_row into N,
    I_normalize_staged_row into I,
    K_normalize_staged_row into K,
    M_normalize_staged_row into M,
    CP_normalize_staged_row into CP.
  subst slot.
  set (values := normalize_row_values K I A C N) in *.
  set (g := normalize_prefix_gcd (Znth I D 0) (K - M) values) in *.
  assert (Hg : 0 < g) by lia.
  set (operand := Znth I C 0) in *.
  set (rem := Z.rem operand g) in *.
  assert (Hscan :
    Znth (K - M) values 0 = operand).
  { unfold values, operand.
    rewrite <- PreH16.
    apply normalize_row_values_constant. }
  assert (Hstep :
    normalize_prefix_gcd (Znth I D 0) (K - M + 1) values = Z.gcd g operand).
  { rewrite normalize_prefix_gcd_step.
    - now rewrite Hscan.
    - unfold values. rewrite normalize_row_values_length. lia. }
  set (next := Z.gcd g rem) in *.
  assert (Hnext : normalize_prefix_gcd (Znth I D 0) (K - M + 1) values = next).
  { rewrite Hstep. unfold next, rem. symmetry. exact (normalize_rem_gcd g operand Hg). }
  assert (Hpositive : 0 < next).
  { rewrite <- Hnext. apply normalize_fold_gcd_positive. exact PreH12. }
  subst x.
  change (store_Z (CP + I * sizeof ("__mpz_struct")) operand)
    with (mpz_store CP I operand).
  sep_apply_l_atomic
    (MpzArray.missing_i_merge_to_full CP I M operand C ltac:(lia)).
  unfold operand.
  rewrite replace_Znth_Znth.
  Exists rem next next.
  split_pure_spatial.
  - sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_normalize_entail_wit_5_3 : normalize_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (pivot_mpz_compact_sign ptr X size PreH2).
  Intros_p Hsign.
  assert (Hzero : X = 0) by (apply (proj1 (proj2 Hsign)); exact PreH1).
  assert (Hprefix :
    G_2 = normalize_prefix_gcd (Znth I_normalize_staged_row D_normalize_staged_row 0) (slot + 1)
      (normalize_row_values K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row C_normalize_staged_row N_normalize_staged_row)).
  { rewrite normalize_prefix_gcd_step by (rewrite normalize_row_values_length; lia).
    rewrite normalize_row_values_column by lia.
    rewrite <- PreH21, <- PreH26, Hzero, <- PreH18.
    rewrite Z.gcd_0_r, Z.abs_eq by lia.
    reflexivity. }
  sep_apply_l_atomic (store_Z_from_fields x ptr size cap X PreH3 PreH2).
  subst x.
  rewrite PreH26.
  assert (Hindex : 0 <= I_normalize_staged_row * K_normalize_staged_row + j < M_normalize_staged_row * K_normalize_staged_row).
  { pose proof (simplex_dimensions_index M_normalize_staged_row (K_normalize_staged_row - M_normalize_staged_row)
      I_normalize_staged_row j PreH4 ltac:(lia) ltac:(lia)) as Hindex.
    replace (M_normalize_staged_row + (K_normalize_staged_row - M_normalize_staged_row)) with K_normalize_staged_row in Hindex by lia.
    exact Hindex. }
  change (store_Z (AP_normalize_staged_row + (I_normalize_staged_row * K_normalize_staged_row + j) * sizeof("__mpz_struct")) (Znth (I_normalize_staged_row * K_normalize_staged_row + j) A_normalize_staged_row 0))
    with (mpz_store AP_normalize_staged_row (I_normalize_staged_row * K_normalize_staged_row + j) (Znth (I_normalize_staged_row * K_normalize_staged_row + j) A_normalize_staged_row 0)).
  sep_apply_l_atomic (MpzArray.missing_i_merge_to_full
    AP_normalize_staged_row (I_normalize_staged_row * K_normalize_staged_row + j) (M_normalize_staged_row * K_normalize_staged_row) (Znth (I_normalize_staged_row * K_normalize_staged_row + j) A_normalize_staged_row 0) A_normalize_staged_row ltac:(lia)).
  rewrite replace_Znth_Znth.
  Exists Rem_2 T_2 G_2.
  split_pure_spatial.
  - sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_5_4 : normalize_entail_wit_5_4.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply_p (pivot_mpz_compact_sign ptr X size PreH2).
  Intros_p Hsign.
  assert (Hzero : X = 0) by (apply (proj1 (proj2 Hsign)); exact PreH1).
  assert (Hprefix :
    G_2 = normalize_prefix_gcd (Znth I_normalize_staged_row D_normalize_staged_row 0) (slot + 1)
      (normalize_row_values K_normalize_staged_row I_normalize_staged_row A_normalize_staged_row C_normalize_staged_row N_normalize_staged_row)).
  { rewrite normalize_prefix_gcd_step by (rewrite normalize_row_values_length; lia).
    rewrite <- PreH13 in PreH19.
    rewrite PreH19, normalize_row_values_constant.
    rewrite <- PreH21, Hzero, <- PreH19, <- PreH18.
    rewrite Z.gcd_0_r, Z.abs_eq by lia.
    reflexivity. }
  sep_apply_l_atomic (store_Z_from_fields x ptr size cap X PreH3 PreH2).
  subst x.
  rewrite PreH21.
  change (store_Z (CP_normalize_staged_row + (I_normalize_staged_row) * sizeof("__mpz_struct")) (Znth (I_normalize_staged_row) C_normalize_staged_row 0))
    with (mpz_store CP_normalize_staged_row (I_normalize_staged_row) (Znth (I_normalize_staged_row) C_normalize_staged_row 0)).
  sep_apply_l_atomic (MpzArray.missing_i_merge_to_full
    CP_normalize_staged_row (I_normalize_staged_row) (M_normalize_staged_row) (Znth (I_normalize_staged_row) C_normalize_staged_row 0) C_normalize_staged_row ltac:(lia)).
  rewrite replace_Znth_Znth.
  Exists Rem_2 T_2 G_2.
  split_pure_spatial.
  - sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_5_5 : normalize_entail_wit_5_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_normalize_staged_row into A,
    C_normalize_staged_row into C,
    D_normalize_staged_row into D,
    N_normalize_staged_row into N,
    I_normalize_staged_row into I,
    K_normalize_staged_row into K,
    M_normalize_staged_row into M,
    AP_normalize_staged_row into AP.
  subst j.
  set (values := normalize_row_values K I A C N) in *.
  set (g := normalize_prefix_gcd (Znth I D 0) slot values) in *.
  assert (Hg : 0 < g) by lia.
  set (column := Znth slot N 0) in *.
  pose proof (simplex_dimensions_index M (K - M) I column
    PreH7 ltac:(lia) ltac:(lia)) as Hindex.
  replace (M + (K - M)) with K in Hindex by lia.
  set (operand := Znth (I * K + column) A 0) in *.
  set (rem := Z.rem operand g) in *.
  assert (Hscan :
    Znth slot values 0 = operand).
  { unfold values, operand, column.
    apply normalize_row_values_column. lia. }
  assert (Hstep :
    normalize_prefix_gcd (Znth I D 0) (slot + 1) values = Z.gcd g operand).
  { rewrite normalize_prefix_gcd_step.
    - now rewrite Hscan.
    - unfold values. rewrite normalize_row_values_length. lia. }
  prop_apply_p (pivot_mpz_compact_sign ptr rem size_2 PreH2).
  Intros_p Hsign.
  assert (Hrem : rem = 0) by (apply Hsign; exact PreH1).
  pose proof (store_Z_from_fields (&("remainder")) ptr size_2 cap_2 rem PreH3 PreH2)
    as Hstore.
  setoid_rewrite (eval_addr (RE_addr_of (LE_var "remainder"))
    (FET_alias "__mpz_struct")) in Hstore.
  sep_apply_l_atomic Hstore.
  assert (Hnext : normalize_prefix_gcd (Znth I D 0) (slot + 1) values = g).
  { rewrite Hstep, <- (normalize_rem_gcd g operand Hg).
    fold rem. rewrite Hrem, Z.gcd_0_r, Z.abs_eq by lia. reflexivity. }
  rewrite Hrem.
  subst x.
  change (store_Z (AP + (I * K + column) * sizeof ("__mpz_struct")) operand)
    with (mpz_store AP (I * K + column) operand).
  sep_apply_l_atomic
    (MpzArray.missing_i_merge_to_full AP (I * K + column) (M * K) operand A Hindex).
  unfold operand.
  rewrite replace_Znth_Znth.
  Exists 0 T_2 g.
  split_pure_spatial.
  - sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_normalize_entail_wit_5_6 : normalize_entail_wit_5_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename A_normalize_staged_row into A,
    C_normalize_staged_row into C,
    D_normalize_staged_row into D,
    N_normalize_staged_row into N,
    I_normalize_staged_row into I,
    K_normalize_staged_row into K,
    M_normalize_staged_row into M,
    CP_normalize_staged_row into CP.
  subst slot.
  set (values := normalize_row_values K I A C N) in *.
  set (g := normalize_prefix_gcd (Znth I D 0) (K - M) values) in *.
  assert (Hg : 0 < g) by lia.
  set (operand := Znth I C 0) in *.
  set (rem := Z.rem operand g) in *.
  assert (Hscan :
    Znth (K - M) values 0 = operand).
  { unfold values, operand.
    rewrite <- PreH16.
    apply normalize_row_values_constant. }
  assert (Hstep :
    normalize_prefix_gcd (Znth I D 0) (K - M + 1) values = Z.gcd g operand).
  { rewrite normalize_prefix_gcd_step.
    - now rewrite Hscan.
    - unfold values. rewrite normalize_row_values_length. lia. }
  prop_apply_p (pivot_mpz_compact_sign ptr rem size_2 PreH2).
  Intros_p Hsign.
  assert (Hrem : rem = 0) by (apply Hsign; exact PreH1).
  pose proof (store_Z_from_fields (&("remainder")) ptr size_2 cap_2 rem PreH3 PreH2)
    as Hstore.
  setoid_rewrite (eval_addr (RE_addr_of (LE_var "remainder"))
    (FET_alias "__mpz_struct")) in Hstore.
  sep_apply_l_atomic Hstore.
  assert (Hnext : normalize_prefix_gcd (Znth I D 0) (K - M + 1) values = g).
  { rewrite Hstep, <- (normalize_rem_gcd g operand Hg).
    fold rem. rewrite Hrem, Z.gcd_0_r, Z.abs_eq by lia. reflexivity. }
  rewrite Hrem.
  subst x.
  change (store_Z (CP + I * sizeof ("__mpz_struct")) operand)
    with (mpz_store CP I operand).
  sep_apply_l_atomic
    (MpzArray.missing_i_merge_to_full CP I M operand C ltac:(lia)).
  unfold operand.
  rewrite replace_Znth_Znth.
  Exists 0 T_2 g.
  split_pure_spatial.
  - sepcon_right_assoc. repeat progress cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_normalize_entail_wit_6_1 : normalize_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match type of PreH16 with
  | G_2 = normalize_prefix_gcd ?den slot (normalize_row_values ?k ?i ?a ?c ?nb) =>
    pose proof (normalize_row_values_length k i a c nb) as Hlength;
    assert (Hrow : G_2 = normalize_row_gcd k i D_normalize_staged_row c a nb)
      by (unfold normalize_row_gcd; rewrite PreH16;
          apply normalize_prefix_gcd_finish;
          [lia | left; lia])
  end.
  unfold store_Z at 1.
  Intros gd gs gcap.
  destruct (Z.eq_dec gs 1) as [-> | Hsize].
  - rewrite (Z.abs_eq G_2) by lia.
    change (Z.abs 1) with 1.
    sep_apply_l_atomic (normalize_single_limb_open gd G_2).
    Intros_p Hlimb.
    Left.
    Exists Rem_2 T_2 gd gcap 1 G_2.
    rewrite ?eval_addr.
    change (Zabs 1) with 1 in *.
    split_pure_spatial.
    + cancel (UIntArray.full gd 1 (G_2 :: nil)).
      cancel.
    + split_pures; dump_pre_spatial; try assumption;
        unfold UINT_MOD in Hlimb; lia.
  - Right.
    Exists Rem_2 T_2 gd gcap gs G_2.
    rewrite ?eval_addr.
    split_pure_spatial.
    + cancel (mpd_store_Z_compact UINT_MOD gd (Zabs G_2) (Zabs gs)).
      cancel.
    + split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_6_2 : normalize_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match type of PreH17 with
  | G_2 = normalize_prefix_gcd ?den slot (normalize_row_values ?k ?i ?a ?c ?nb) =>
    pose proof (normalize_row_values_length k i a c nb) as Hlength;
    assert (Hrow : G_2 = normalize_row_gcd k i D_normalize_staged_row c a nb)
      by (unfold normalize_row_gcd; rewrite PreH17;
          apply normalize_prefix_gcd_finish;
          [lia | right; lia])
  end.
  Left.
  Exists Rem_2 T_2 gd_2 gcap_2 gs_2 G_2.
  change (replace_Znth 0 G_2 (G_2 :: nil)) with (G_2 :: nil).
  split_pure_spatial.
  - cancel (UIntArray.full gd_2 1 (G_2 :: nil)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_6_3 : normalize_entail_wit_6_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match type of PreH17 with
  | G_2 = normalize_prefix_gcd ?den slot (normalize_row_values ?k ?i ?a ?c ?nb) =>
    pose proof (normalize_row_values_length k i a c nb) as Hlength;
    assert (Hrow : G_2 = normalize_row_gcd k i D_normalize_staged_row c a nb)
      by (unfold normalize_row_gcd; rewrite PreH17;
          apply normalize_prefix_gcd_finish;
          [lia | right; lia])
  end.
  Left.
  Exists Rem_2 T_2 gd_2 gcap_2 gs_2 G_2.
  change (replace_Znth 0 G_2 (G_2 :: nil)) with (G_2 :: nil).
  split_pure_spatial.
  - cancel (UIntArray.full gd_2 1 (G_2 :: nil)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_normalize_entail_wit_7_1 : normalize_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (normalize_row_gcd_exact K_normalize_staged_row I_normalize_staged_row
    D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row
    N_normalize_staged_row PreH7) as [_ [Hden _]].
  rewrite <- PreH14 in Hden.
  Exists Rem_2 T_2 G_2.
  split_pure_spatial.
  - rewrite <- (eval_addr (RE_addr_of (LE_var "g"))
      (FET_alias "__mpz_struct")).
    sep_apply (store_Z_from_fields (&("g")) gd gs gcap G_2 PreH16 PreH15).
    rewrite (eval_addr (RE_addr_of (LE_var "g"))
      (FET_alias "__mpz_struct")).
    sep_apply (MpzArray.full_split_to_missing_i DP_normalize_staged_row
      I_normalize_staged_row M_normalize_staged_row D_normalize_staged_row 0 ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_normalize_entail_wit_7_2 : normalize_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (normalize_row_gcd_exact K_normalize_staged_row I_normalize_staged_row
    D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row
    N_normalize_staged_row PreH8) as [_ [Hden _]].
  rewrite <- PreH15 in Hden.
  subst gs.
  Exists Rem_2 T_2 G_2.
  split_pure_spatial.
  - replace (replace_Znth 0 G_2 (G_2 :: nil)) with (G_2 :: nil) by reflexivity.
    sep_apply (normalize_single_limb_close gd G_2 ltac:(unfold UINT_MOD; lia)).
    replace (mpd_store_Z_compact UINT_MOD gd G_2 1)
      with (mpd_store_Z_compact UINT_MOD gd (Z.abs G_2) (Z.abs 1))
      by (rewrite Z.abs_eq by lia; reflexivity).
    rewrite <- (eval_addr (RE_addr_of (LE_var "g"))
      (FET_alias "__mpz_struct")).
    sep_apply (store_Z_from_fields (&("g")) gd 1 gcap G_2 PreH17 PreH16).
    rewrite (eval_addr (RE_addr_of (LE_var "g"))
      (FET_alias "__mpz_struct")).
    sep_apply (MpzArray.full_split_to_missing_i DP_normalize_staged_row
      I_normalize_staged_row M_normalize_staged_row D_normalize_staged_row 0 ltac:(lia)).
    unfold mpz_store, mpz_sizeof.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_normalize_entail_wit_8 : normalize_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst G_2.
  set (g := normalize_row_gcd K_normalize_staged_row I_normalize_staged_row
    D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row
    N_normalize_staged_row).
  set (q := Z.quot (Znth I_normalize_staged_row D_normalize_staged_row 0) g).
  Exists Rem_2 q A_normalize_staged_row C_normalize_staged_row
    (replace_Znth I_normalize_staged_row q D_normalize_staged_row) g.
  split_pure_spatial.
  - change (store_Z (DP_normalize_staged_row +
        I_normalize_staged_row * sizeof("__mpz_struct")) q)
      with (mpz_store DP_normalize_staged_row I_normalize_staged_row q).
    sep_apply (MpzArray.missing_i_merge_to_full DP_normalize_staged_row
      I_normalize_staged_row M_normalize_staged_row q D_normalize_staged_row ltac:(lia)).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    rewrite Z.min_l by lia.
    apply normalize_coeff_prefix_empty.
    assumption.
Qed.

Lemma proof_of_normalize_entail_wit_9_1 : normalize_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists Rem_2 T_2 Aa_2 Ca_2 Da_2 G_2.
  split_pure_spatial.
  - sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_normalize_entail_wit_9_2 : normalize_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (normalize_slot_range K_normalize_staged_row B_normalize_staged_row
    R_normalize_staged_row N_normalize_staged_row slot PreH7 ltac:(lia))
    as [[Hcolumn_nonneg Hcolumn_lt] Hrow].
  Exists Rem_2 T_2 (Znth slot N_normalize_staged_row 0) Aa_2 Ca_2 Da_2 G_2.
  split_pure_spatial.
  - sepcon_right_assoc; cancel; reflexivity.
  - split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.

Lemma proof_of_normalize_entail_wit_10_1 : normalize_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename I_normalize_staged_row into i, M_normalize_staged_row into m,
    K_normalize_staged_row into k, CP_normalize_staged_row into cp,
    C_normalize_staged_row into c, D_normalize_staged_row into d,
    A_normalize_staged_row into a, N_normalize_staged_row into nb.
  subst Ca_2.
  destruct (normalize_row_gcd_exact k i d c a nb PreH7) as [_ [_ [Hconstant _]]].
  rewrite <- PreH16 in Hconstant.
  Exists Rem_2 T_2 (Znth i c 0) Aa_2 c Da_2 G_2.
  split_pure_spatial.
  - pose proof (MpzArray.full_split_to_missing_i cp i m c 0 ltac:(lia)) as Hsplit.
    unfold mpz_store, mpz_sizeof in Hsplit.
    sep_apply_l_atomic Hsplit.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity.
    apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_normalize_entail_wit_10_2 : normalize_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename N_normalize_staged_row into N, R_normalize_staged_row into R,
    B_normalize_staged_row into B, A_normalize_staged_row into A,
    C_normalize_staged_row into C, D_normalize_staged_row into D,
    AP_normalize_staged_row into AP, I_normalize_staged_row into I,
    K_normalize_staged_row into K, M_normalize_staged_row into M.
  assert (Hslot : 0 <= slot < Zlength N) by lia.
  destruct (normalize_slot_range K B R N slot PreH8 Hslot) as [Hcol Hnonbasic].
  pose proof (simplex_dimensions_index M (K - M) I (Znth slot N 0)
    PreH4 ltac:(lia) ltac:(lia)) as Hindex.
  replace (M + (K - M)) with K in Hindex by lia.
  assert (Hraw : unsigned_last_nbits (I * K) 32 = I * K).
  { apply unsigned_last_nbits_eq.
    destruct (simplex_dimensions_bounds M (K - M) PreH4) as [Htotal _].
    replace (M + (K - M)) with K in Htotal by lia.
    assert (0 <= I * K) by (apply Z.mul_nonneg_nonneg; lia).
    destruct Htotal as [_ Htotal].
    change (M * K <= 2147483647) in Htotal.
    change (0 <= I * K < 4294967296).
    lia. }
  rewrite Z.min_l in PreH22 by lia.
  pose proof (normalize_coeff_prefix_unvisited M K I G_2 slot A N Aa_2
    (proj1 PreH8) PreH22 Hslot Hindex) as Hunvisited.
  assert (Hexact : pivot_divides_exactly (Znth (I * K + Znth slot N 0) Aa_2 0) G_2).
  { rewrite Hunvisited, PreH18.
    apply (proj2 (proj2 (proj2 (normalize_row_gcd_exact K I D C A N PreH9)))).
    apply SumLib.ZRange.Znth_In_Zlength. exact Hslot. }
  rewrite PreH25, Hraw.
  set (p := I * K + Znth slot N 0) in *.
  Exists Rem_2 T_2 (Znth slot N 0) (Znth p Aa_2 0) Aa_2 Ca_2 Da_2 G_2.
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.full_split_to_missing_i AP p (M * K) Aa_2 0 Hindex).
    unfold mpz_store, mpz_sizeof, p. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    all: try (rewrite Z.min_l by lia; exact PreH22).
    apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_normalize_entail_wit_11_1 : normalize_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename N_normalize_staged_row into N, R_normalize_staged_row into R,
    B_normalize_staged_row into B, A_normalize_staged_row into A,
    C_normalize_staged_row into C, D_normalize_staged_row into D,
    AP_normalize_staged_row into AP, I_normalize_staged_row into I,
    K_normalize_staged_row into K, M_normalize_staged_row into M.
  assert (Hslot : 0 <= slot < Zlength N) by lia.
  destruct (normalize_slot_range K B R N slot PreH8 Hslot) as [Hcol Hnonbasic].
  pose proof (simplex_dimensions_index M (K - M) I (Znth slot N 0)
    PreH4 ltac:(lia) ltac:(lia)) as Hindex.
  replace (M + (K - M)) with K in Hindex by lia.
  rewrite Z.min_l in PreH22 by lia.
  pose proof (normalize_coeff_prefix_unvisited M K I G_2 slot A N Aa_2
    (proj1 PreH8) PreH22 Hslot Hindex) as Hunvisited.
  subst x j Ca_2.
  rewrite <- PreH18.
  set (p := I * K + Znth slot N 0) in *.
  set (q := Z.quot (Znth p A 0) G_2).
  change (store_Z (AP + p * sizeof("__mpz_struct")) (Znth p Aa_2 0 ÷ G_2))
    with (mpz_store AP p (Z.quot (Znth p Aa_2 0) G_2)).
  change (store_Z (&("tmp")) (Znth p Aa_2 0 ÷ G_2))
    with (store_Z (&("tmp")) (Z.quot (Znth p Aa_2 0) G_2)).
  rewrite Hunvisited. fold q.
  Exists Rem_2 q (replace_Znth p q Aa_2) C Da_2 G_2.
  rewrite Z.min_l by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (MpzArray.missing_i_merge_to_full AP p (M * K) q Aa_2 Hindex).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    apply (normalize_coeff_prefix_write M K I G_2 slot A N Aa_2 PreH22 Hslot Hindex).
Qed.

Lemma proof_of_normalize_entail_wit_11_2 : normalize_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename I_normalize_staged_row into i, M_normalize_staged_row into m,
    CP_normalize_staged_row into cp, C_normalize_staged_row into c.
  subst Ca_2 x.
  set (q := Z.quot (Znth i c 0) G_2).
  Exists Rem_2 q Aa_2 (replace_Znth i q c) Da_2 G_2.
  split_pure_spatial.
  - rewrite <- PreH18.
    fold q.
    pose proof (MpzArray.missing_i_merge_to_full cp i m q c ltac:(lia)) as Hmerge.
    unfold mpz_store, mpz_sizeof in Hmerge.
    sep_apply_l_atomic Hmerge.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    rewrite Z.min_r by lia.
    rewrite Z.min_r in PreH22 by lia.
    exact PreH22.
Qed.

Lemma proof_of_normalize_entail_wit_11_3 : normalize_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename N_normalize_staged_row into N, R_normalize_staged_row into R,
    B_normalize_staged_row into B, A_normalize_staged_row into A,
    C_normalize_staged_row into C, D_normalize_staged_row into D,
    AP_normalize_staged_row into AP, I_normalize_staged_row into I,
    K_normalize_staged_row into K, M_normalize_staged_row into M.
  assert (Hslot : 0 <= slot < Zlength N) by lia.
  destruct (normalize_slot_range K B R N slot PreH8 Hslot) as [Hcol Hnonbasic].
  pose proof (simplex_dimensions_index M (K - M) I (Znth slot N 0)
    PreH4 ltac:(lia) ltac:(lia)) as Hindex.
  replace (M + (K - M)) with K in Hindex by lia.
  rewrite Z.min_l in PreH22 by lia.
  pose proof (normalize_coeff_prefix_unvisited M K I G_2 slot A N Aa_2
    (proj1 PreH8) PreH22 Hslot Hindex) as Hunvisited.
  prop_apply_p (pivot_mpz_compact_sign ptr X size PreH2).
  Intros_p Hsign.
  assert (Hzero : X = 0) by (apply (proj1 (proj2 Hsign)); exact PreH1).
  subst x j Ca_2.
  set (p := I * K + Znth slot N 0) in *.
  assert (HcurZero : Znth p Aa_2 0 = 0) by lia.
  assert (HinputZero : Znth p A 0 = 0) by lia.
  Exists Rem_2 T_2 Aa_2 C Da_2 G_2.
  rewrite Z.min_l by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (store_Z_from_fields (AP + p * sizeof("__mpz_struct"))
      ptr size cap X PreH3 PreH2).
    change (store_Z (AP + p * sizeof("__mpz_struct")) X) with (mpz_store AP p X).
    sep_apply_l_atomic (MpzArray.missing_i_merge_to_full AP p (M * K) X Aa_2 Hindex).
    rewrite PreH32, ListLib.Base.Positional.replace_Znth_Znth.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    apply (normalize_coeff_prefix_zero M K I G_2 slot A N Aa_2
      PreH22 Hslot Hindex ltac:(lia) HinputZero HcurZero).
Qed.

Lemma proof_of_normalize_entail_wit_11_4 : normalize_entail_wit_11_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename I_normalize_staged_row into i, M_normalize_staged_row into m,
    CP_normalize_staged_row into cp, C_normalize_staged_row into c.
  subst Ca_2 x.
  prop_apply_p (pivot_mpz_compact_sign ptr X size PreH2).
  Intros_p Hsign.
  assert (Hzero : X = 0) by (apply (proj1 (proj2 Hsign)); exact PreH1).
  assert (Hconstant : Znth i c 0 = 0) by congruence.
  Exists Rem_2 T_2 Aa_2 c Da_2 G_2.
  split_pure_spatial.
  - sep_apply_l_atomic (store_Z_from_fields
      (cp + i * sizeof ("__mpz_struct")) ptr size cap X PreH3 PreH2).
    pose proof (MpzArray.missing_i_merge_to_full cp i m X c ltac:(lia)) as Hmerge.
    unfold mpz_store, mpz_sizeof in Hmerge.
    rewrite PreH27, replace_Znth_Znth in Hmerge.
    rewrite PreH27.
    sep_apply_l_atomic Hmerge.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + pose proof (replace_Znth_Znth i c 0) as Hsame.
      rewrite Hconstant in Hsame |- *.
      rewrite Z.quot_0_l by lia.
      symmetry. exact Hsame.
    + rewrite Z.min_r by lia.
      rewrite Z.min_r in PreH22 by lia.
      exact PreH22.
Qed.

Lemma proof_of_normalize_entail_wit_12_1_split_goal_1 : normalize_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold normalize_result.
  cbn zeta.
  rewrite <- PreH16.
  split; [exact PreH17 |].
  split; [exact PreH19 |].
  rewrite PreH11.
  rewrite Z.min_r in PreH20 by lia.
  exact PreH20.
Qed.

Lemma proof_of_normalize_entail_wit_12_1 : normalize_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_normalize_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_normalize_entail_wit_12_2 : normalize_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlimb : 1 <= G_2 < UINT_MOD) by (unfold UINT_MOD; lia).
  assert (Hmag : Z.abs G_2 = G_2) by (apply Z.abs_eq; lia).
  assert (Hsize : Z.abs gs = 1) by (rewrite PreH2; reflexivity).
  pose proof (store_Z_from_fields (&( "g" )) gd gs gcap G_2 PreH17 PreH16) as Hstore.
  rewrite Hmag, Hsize in Hstore.
  rewrite (eval_addr (RE_addr_of (LE_var "g")) (FET_alias "__mpz_struct")) in Hstore.
  rewrite Hsize.
  change (replace_Znth 0 G_2 (G_2 :: nil)) with (G_2 :: nil).
  sep_apply_l_atomic (normalize_single_limb_close gd G_2 Hlimb).
  sep_apply_l_atomic Hstore.
  Exists Rem_2 T_2 G_2 D_normalize_staged_row C_normalize_staged_row A_normalize_staged_row.
  split_pure_spatial.
  - sepcon_right_assoc; cancel; reflexivity.
  - dump_pre_spatial. apply normalize_result_unit; [congruence | assumption].
Qed.

Lemma proof_of_normalize_partial_solve_wit_12_pure_split_goal_1 : normalize_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_normalize_partial_solve_wit_12_pure : normalize_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_normalize_partial_solve_wit_12_pure_split_goal_1.
Qed.

Lemma proof_of_normalize_partial_solve_wit_13_pure_split_goal_1 : normalize_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_normalize_partial_solve_wit_13_pure_split_goal_2 : normalize_partial_solve_wit_13_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite <- PreH31, <- PreH30.
  lia.
Qed.

Lemma proof_of_normalize_partial_solve_wit_13_pure : normalize_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_normalize_partial_solve_wit_13_pure_split_goal_1.
  - Goal_apply proof_of_normalize_partial_solve_wit_13_pure_split_goal_2.
Qed.

