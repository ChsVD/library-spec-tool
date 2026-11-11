From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_deduction Require Import simplex_deduction_goal.
From SimpleC.EE.Applications_human.simplex_deduction Require Import simplex_deduction_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_initialize.simplex_initialize_lib.
Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib.
Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib.
Require Import SimpleC.EE.Applications_human.simplex_check.simplex_check_lib.
Require Import SimpleC.EE.Applications_human.simplex_deduction.simplex_deduction_lib.
Local Open Scope sac.

Lemma proof_of_simplex_deduction_entail_wit_1_nullcoef_reject_split_goal_1 : simplex_deduction_entail_wit_1_nullcoef_reject_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
destruct (Z.eq_dec M_nullcoef_reject 0) as [Hz|Hnz].
- subst M_nullcoef_reject; congruence.
- specialize (PreH20 0 ltac:(lia)). intuition congruence.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_1_nullcoef_reject : simplex_deduction_entail_wit_1_nullcoef_reject.
Proof.
aggressive_pre_process.
Goal_apply proof_of_simplex_deduction_entail_wit_1_nullcoef_reject_split_goal_1.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_2_bounded_prefix_reject_split_goal_1 : simplex_deduction_entail_wit_2_bounded_prefix_reject_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
specialize (PreH20 0 ltac:(lia)). intuition congruence.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_2_bounded_prefix_reject : simplex_deduction_entail_wit_2_bounded_prefix_reject.
Proof.
aggressive_pre_process.
Goal_apply proof_of_simplex_deduction_entail_wit_2_bounded_prefix_reject_split_goal_1.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_3_complete_min : simplex_deduction_entail_wit_3_complete_min.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 0 ltac:(lia)) as Hhead.
  assert (Hnon:list_pre<>0) by (rewrite PreH17; tauto).
  Right.
  Exists 0 y_2 x_2.
  subst c_pre s_pre inputs_pre pivot_limit_pre.
  split_pure_spatial.
  - sepcon_right_assoc. cancel; reflexivity.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_1 : simplex_deduction_entail_wit_4_zero_negative_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_negative.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_2 : simplex_deduction_entail_wit_4_zero_negative_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_negative.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_3 : simplex_deduction_entail_wit_4_zero_negative_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_negative.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_4 : simplex_deduction_entail_wit_4_zero_negative_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_negative.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_5 : simplex_deduction_entail_wit_4_zero_negative_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_negative.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_spatial : simplex_deduction_entail_wit_4_zero_negative_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst M_zero_negative.
  unfold simplex_deduction_workspace, simplex_init_input.
  simpl. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_4_zero_negative : simplex_deduction_entail_wit_4_zero_negative.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_3.
  - Goal_apply proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_4.
  - Goal_apply proof_of_simplex_deduction_entail_wit_4_zero_negative_split_goal_5.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_1 : simplex_deduction_entail_wit_5_zero_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_normal.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_2 : simplex_deduction_entail_wit_5_zero_normal_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_normal.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_3 : simplex_deduction_entail_wit_5_zero_normal_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_normal.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_4 : simplex_deduction_entail_wit_5_zero_normal_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_normal.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_5 : simplex_deduction_entail_wit_5_zero_normal_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: subst M_zero_normal.
  all: dump_pre_spatial.
  all: simpl in *; intuition lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_spatial : simplex_deduction_entail_wit_5_zero_normal_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst M_zero_normal.
  unfold simplex_deduction_workspace, simplex_init_input.
  simpl. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_5_zero_normal : simplex_deduction_entail_wit_5_zero_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_3.
  - Goal_apply proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_4.
  - Goal_apply proof_of_simplex_deduction_entail_wit_5_zero_normal_split_goal_5.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_6_matrix_negative : simplex_deduction_entail_wit_6_matrix_negative.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 0 ltac:(lia)) as Hhead.
  assert (Hnon:list_pre<>0) by (rewrite PreH17; tauto).
  Right.
  Exists 0.
  subst c_pre s_pre inputs_pre pivot_limit_pre.
  split_pure_spatial.
  - sepcon_right_assoc. cancel; reflexivity.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_7_matrix_normal : simplex_deduction_entail_wit_7_matrix_normal.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH20 0 ltac:(lia)) as Hhead.
  assert (Hnon:list_pre<>0) by (rewrite PreH17; tauto).
  Right.
  Exists 0.
  subst c_pre s_pre inputs_pre pivot_limit_pre.
  split_pure_spatial.
  - sepcon_right_assoc. cancel; reflexivity.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_1 : simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 all: try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_2 : simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 all: try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_spatial : simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 assert (Hmem: In (simplex_deduction_coef_address p) PS_nullcoef_reject).
 { rewrite PreH24. destruct (Z_lt_ge_dec rows M_nullcoef_reject).
 - pose proof (PreH16 rows ltac:(lia)) as HH. tauto.
 - replace rows with M_nullcoef_reject by lia. exact PreH20. }
unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_nullcoef_reject z)) PS_nullcoef_reject (simplex_deduction_coef_address p) PreH14 Hmem).
 unfold simplex_deduction_coef_address. sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_8_nullcoef_reject : simplex_deduction_entail_wit_8_nullcoef_reject.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_spatial.
 - Goal_apply proof_of_simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_1.
 - Goal_apply proof_of_simplex_deduction_entail_wit_8_nullcoef_reject_split_goal_2.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_9_bounded_prefix_reject : simplex_deduction_entail_wit_9_bounded_prefix_reject.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 destruct (Z_lt_ge_dec rows 16) as [Hlt|Hge].
 - Left.
 assert (Hr: rows < M_bounded_prefix_reject).
 { lia. }
 assert (Hmem: In (simplex_deduction_coef_address p) PS_bounded_prefix_reject).
 { rewrite PreH22. pose proof (PreH16 rows ltac:(lia)) as HH. tauto. }
 split_pure_spatial.
 + unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_bounded_prefix_reject z)) PS_bounded_prefix_reject (simplex_deduction_coef_address p) PreH14 Hmem).
 unfold simplex_deduction_coef_address. sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
 - Right.
 split_pure_spatial.
 + sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_10_complete_min : simplex_deduction_entail_wit_10_complete_min.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 destruct (Z_lt_ge_dec rows 16) as [Hlt|Hge].
 - Left.
 Exists y_2 x_2.
 assert (Hr: rows < M_complete_min).
 { destruct (Z_lt_ge_dec rows M_complete_min); [assumption|].
 assert (He: rows=M_complete_min) by lia. rewrite He, PreH18 in PreH26. contradiction. }
 assert (Hmem: In (simplex_deduction_coef_address p) PS_complete_min).
 { rewrite PreH26. pose proof (PreH16 rows ltac:(lia)) as HH. tauto. }
 split_pure_spatial.
 + unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_complete_min z)) PS_complete_min (simplex_deduction_coef_address p) PreH14 Hmem).
 unfold simplex_deduction_coef_address. sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
 - Right.
 Exists y_2 x_2.
 split_pure_spatial.
 + sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_11_matrix_negative : simplex_deduction_entail_wit_11_matrix_negative.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 destruct (Z_lt_ge_dec rows 16) as [Hlt|Hge].
 - Left.
 assert (Hr: rows < M_matrix_negative).
 { destruct (Z_lt_ge_dec rows M_matrix_negative); [assumption|].
 assert (He: rows=M_matrix_negative) by lia. rewrite He, PreH18 in PreH24. contradiction. }
 assert (Hmem: In (simplex_deduction_coef_address p) PS_matrix_negative).
 { rewrite PreH24. pose proof (PreH16 rows ltac:(lia)) as HH. tauto. }
 split_pure_spatial.
 + unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_matrix_negative z)) PS_matrix_negative (simplex_deduction_coef_address p) PreH14 Hmem).
 unfold simplex_deduction_coef_address. sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
 - Right.
 split_pure_spatial.
 + sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_12_matrix_normal : simplex_deduction_entail_wit_12_matrix_normal.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 destruct (Z_lt_ge_dec rows 16) as [Hlt|Hge].
 - Left.
 assert (Hr: rows < M_matrix_normal).
 { destruct (Z_lt_ge_dec rows M_matrix_normal); [assumption|].
 assert (He: rows=M_matrix_normal) by lia. rewrite He, PreH18 in PreH24. contradiction. }
 assert (Hmem: In (simplex_deduction_coef_address p) PS_matrix_normal).
 { rewrite PreH24. pose proof (PreH16 rows ltac:(lia)) as HH. tauto. }
 split_pure_spatial.
 + unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_matrix_normal z)) PS_matrix_normal (simplex_deduction_coef_address p) PreH14 Hmem).
 unfold simplex_deduction_coef_address. sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
 - Right.
 split_pure_spatial.
 + sepcon_right_assoc. cancel; reflexivity.
 + split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_1 : simplex_deduction_entail_wit_13_matrix_normal_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_matrix_normal) by (assert (rows <> M_matrix_normal) by (intro E; subst rows; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_2 : simplex_deduction_entail_wit_13_matrix_normal_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_matrix_normal) by (assert (rows <> M_matrix_normal) by (intro E; subst rows; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_3 : simplex_deduction_entail_wit_13_matrix_normal_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_matrix_normal) by (assert (rows <> M_matrix_normal) by (intro E; subst rows; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_spatial : simplex_deduction_entail_wit_13_matrix_normal_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (HR: rows < M_matrix_normal) by (assert (rows <> M_matrix_normal) by (intro E; subst rows; congruence); lia).
pose proof (PreH16 rows ltac:(lia)) as HT.
 assert (HI: In (simplex_deduction_coef_address p) PS_matrix_normal) by (rewrite PreH24; tauto).
 unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 unfold simplex_deduction_coef_address in *.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_matrix_normal z)) PS_matrix_normal (&(p #"InequList" ->ₛ "coef")) PreH14 HI).
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_13_matrix_normal : simplex_deduction_entail_wit_13_matrix_normal.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_spatial CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_1 CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_2 CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_13_matrix_normal_split_goal_3 CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_1 : simplex_deduction_entail_wit_14_matrix_negative_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_matrix_negative) by (assert (rows <> M_matrix_negative) by (intro E; subst rows; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_2 : simplex_deduction_entail_wit_14_matrix_negative_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_matrix_negative) by (assert (rows <> M_matrix_negative) by (intro E; subst rows; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_3 : simplex_deduction_entail_wit_14_matrix_negative_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_matrix_negative) by (assert (rows <> M_matrix_negative) by (intro E; subst rows; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_spatial : simplex_deduction_entail_wit_14_matrix_negative_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (HR: rows < M_matrix_negative) by (assert (rows <> M_matrix_negative) by (intro E; subst rows; congruence); lia).
pose proof (PreH16 rows ltac:(lia)) as HT.
 assert (HI: In (simplex_deduction_coef_address p) PS_matrix_negative) by (rewrite PreH24; tauto).
 unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 unfold simplex_deduction_coef_address in *.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_matrix_negative z)) PS_matrix_negative (&(p #"InequList" ->ₛ "coef")) PreH14 HI).
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_14_matrix_negative : simplex_deduction_entail_wit_14_matrix_negative.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_spatial CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_1 CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_2 CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_14_matrix_negative_split_goal_3 CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_15_complete_min : simplex_deduction_entail_wit_15_complete_min.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (HR: rows < M_complete_min) by (assert (rows <> M_complete_min) by (intro E; subst rows; congruence); lia).
Exists y_2 x_2.
split_pure_spatial.
- pose proof (PreH16 rows ltac:(lia)) as HT.
 assert (HI: In (simplex_deduction_coef_address p) PS_complete_min) by (rewrite PreH26; tauto).
 unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 unfold simplex_deduction_coef_address in *.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_complete_min z)) PS_complete_min (&(p #"InequList" ->ₛ "coef")) PreH14 HI).
 sepcon_right_assoc. cancel; reflexivity.
- split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_1 : simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_bounded_prefix_reject) by lia.
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_2 : simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_bounded_prefix_reject) by lia.
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_spatial : simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (HR: rows < M_bounded_prefix_reject) by lia.
pose proof (PreH16 rows ltac:(lia)) as HT.
 assert (HI: In (simplex_deduction_coef_address p) PS_bounded_prefix_reject) by (rewrite PreH22; tauto).
 unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 unfold simplex_deduction_coef_address in *.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_bounded_prefix_reject z)) PS_bounded_prefix_reject (&(p #"InequList" ->ₛ "coef")) PreH14 HI).
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject : simplex_deduction_entail_wit_16_bounded_prefix_reject.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_spatial C_bounded_prefix_reject L_bounded_prefix_reject N_bounded_prefix_reject M_bounded_prefix_reject IV_bounded_prefix_reject PV_bounded_prefix_reject IS_bounded_prefix_reject PS_bounded_prefix_reject P_bounded_prefix_reject A_bounded_prefix_reject list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_1 C_bounded_prefix_reject L_bounded_prefix_reject N_bounded_prefix_reject M_bounded_prefix_reject IV_bounded_prefix_reject PV_bounded_prefix_reject IS_bounded_prefix_reject PS_bounded_prefix_reject P_bounded_prefix_reject A_bounded_prefix_reject list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_16_bounded_prefix_reject_split_goal_2 C_bounded_prefix_reject L_bounded_prefix_reject N_bounded_prefix_reject M_bounded_prefix_reject IV_bounded_prefix_reject PV_bounded_prefix_reject IS_bounded_prefix_reject PS_bounded_prefix_reject P_bounded_prefix_reject A_bounded_prefix_reject list rows p).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_1 : simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_nullcoef_reject) by (assert (rows <> M_nullcoef_reject) by (intro E; subst rows; rewrite PreH24 in PreH1; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_2 : simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_nullcoef_reject) by (assert (rows <> M_nullcoef_reject) by (intro E; subst rows; rewrite PreH24 in PreH1; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_3 : simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: dump_pre_spatial.
all: assert (HR: rows < M_nullcoef_reject) by (assert (rows <> M_nullcoef_reject) by (intro E; subst rows; rewrite PreH24 in PreH1; congruence); lia).
all: first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_spatial : simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (HR: rows < M_nullcoef_reject) by (assert (rows <> M_nullcoef_reject) by (intro E; subst rows; rewrite PreH24 in PreH1; congruence); lia).
pose proof (PreH16 rows ltac:(lia)) as HT.
 assert (HI: In (simplex_deduction_coef_address p) PS_nullcoef_reject) by (rewrite PreH24; tauto).
 unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
 unfold simplex_deduction_coef_address in *.
 rewrite (deduction_support_remove (fun z => z # Ptr |-> (PV_nullcoef_reject z)) PS_nullcoef_reject (&(p #"InequList" ->ₛ "coef")) PreH14 HI).
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_17_nullcoef_reject : simplex_deduction_entail_wit_17_nullcoef_reject.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_spatial C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_1 C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_2 C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p).
- Goal_apply (proof_of_simplex_deduction_entail_wit_17_nullcoef_reject_split_goal_3 C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_18_nullcoef_reject : simplex_deduction_entail_wit_18_nullcoef_reject.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (PreH15 rows ltac:(lia)) as Hrow.
 pose proof (PreH16 rows j ltac:(lia)) as Hcell.
 assert (HP:In (simplex_deduction_coef_address p) PS_nullcoef_reject) by (subst p;tauto).
 assert (HI:In (PV_nullcoef_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_nullcoef_reject) by (subst p;tauto).
 assert (HV:IV_nullcoef_reject(PV_nullcoef_reject(simplex_deduction_coef_address p)+j*sizeof(INT))=Znth(rows*9+j) A_nullcoef_reject 0) by (subst p;tauto).
 unfold simplex_deduction_ptrs,simplex_deduction_ints,
 simplex_deduction_ptrs_without,simplex_deduction_ints_without.
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Ptr |-> (PV_nullcoef_reject x)) PS_nullcoef_reject (simplex_deduction_coef_address p) PreH13 HP)).
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Int |-> (IV_nullcoef_reject x)) IS_nullcoef_reject (PV_nullcoef_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) PreH14 HI)).
 sep_apply_l_atomic (proj1(workspace_focus__workspace_focus C_nullcoef_reject A_nullcoef_reject M_nullcoef_reject N_nullcoef_reject rows j ltac:(lia) ltac:(lia))).
 unfold simplex_deduction_coef_address in *.
 replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring.
 split_pure_spatial; [sepcon_right_assoc;cancel;reflexivity | split_pures;dump_pre_spatial;auto].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_19_bounded_prefix_reject : simplex_deduction_entail_wit_19_bounded_prefix_reject.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (PreH15 rows ltac:(lia)) as Hrow.
 pose proof (PreH16 rows j ltac:(lia)) as Hcell.
 assert (HP:In (simplex_deduction_coef_address p) PS_bounded_prefix_reject) by (subst p;tauto).
 assert (HI:In (PV_bounded_prefix_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_bounded_prefix_reject) by (subst p;tauto).
 assert (HV:IV_bounded_prefix_reject(PV_bounded_prefix_reject(simplex_deduction_coef_address p)+j*sizeof(INT))=Znth(rows*9+j) A_bounded_prefix_reject 0) by (subst p;tauto).
 unfold simplex_deduction_ptrs,simplex_deduction_ints,
 simplex_deduction_ptrs_without,simplex_deduction_ints_without.
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Ptr |-> (PV_bounded_prefix_reject x)) PS_bounded_prefix_reject (simplex_deduction_coef_address p) PreH13 HP)).
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Int |-> (IV_bounded_prefix_reject x)) IS_bounded_prefix_reject (PV_bounded_prefix_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) PreH14 HI)).
 sep_apply_l_atomic (proj1(workspace_focus__workspace_focus C_bounded_prefix_reject A_bounded_prefix_reject M_bounded_prefix_reject N_bounded_prefix_reject rows j ltac:(lia) ltac:(lia))).
 unfold simplex_deduction_coef_address in *.
 replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring.
 split_pure_spatial; [sepcon_right_assoc;cancel;reflexivity | split_pures;dump_pre_spatial;auto].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_20_complete_min : simplex_deduction_entail_wit_20_complete_min.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (PreH15 rows ltac:(lia)) as Hrow.
 pose proof (PreH16 rows j ltac:(lia)) as Hcell.
 assert (HP:In (simplex_deduction_coef_address p) PS_complete_min) by (subst p;tauto).
 assert (HI:In (PV_complete_min(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_complete_min) by (subst p;tauto).
 assert (HV:IV_complete_min(PV_complete_min(simplex_deduction_coef_address p)+j*sizeof(INT))=Znth(rows*9+j) A_complete_min 0) by (subst p;tauto).
 unfold simplex_deduction_ptrs,simplex_deduction_ints,
 simplex_deduction_ptrs_without,simplex_deduction_ints_without.
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Ptr |-> (PV_complete_min x)) PS_complete_min (simplex_deduction_coef_address p) PreH13 HP)).
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Int |-> (IV_complete_min x)) IS_complete_min (PV_complete_min(simplex_deduction_coef_address p)+j*sizeof(INT)) PreH14 HI)).
 sep_apply_l_atomic (proj1(workspace_focus__workspace_focus C_complete_min A_complete_min M_complete_min N_complete_min rows j ltac:(lia) ltac:(lia))).
 unfold simplex_deduction_coef_address in *.
 replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring.
 Exists y_2 x_2.
 split_pure_spatial; [sepcon_right_assoc;cancel;reflexivity | split_pures;dump_pre_spatial;auto].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_21_matrix_negative : simplex_deduction_entail_wit_21_matrix_negative.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (PreH15 rows ltac:(lia)) as Hrow.
 pose proof (PreH16 rows j ltac:(lia)) as Hcell.
 assert (HP:In (simplex_deduction_coef_address p) PS_matrix_negative) by (subst p;tauto).
 assert (HI:In (PV_matrix_negative(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_matrix_negative) by (subst p;tauto).
 assert (HV:IV_matrix_negative(PV_matrix_negative(simplex_deduction_coef_address p)+j*sizeof(INT))=Znth(rows*9+j) A_matrix_negative 0) by (subst p;tauto).
 unfold simplex_deduction_ptrs,simplex_deduction_ints,
 simplex_deduction_ptrs_without,simplex_deduction_ints_without.
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Ptr |-> (PV_matrix_negative x)) PS_matrix_negative (simplex_deduction_coef_address p) PreH13 HP)).
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Int |-> (IV_matrix_negative x)) IS_matrix_negative (PV_matrix_negative(simplex_deduction_coef_address p)+j*sizeof(INT)) PreH14 HI)).
 sep_apply_l_atomic (proj1(workspace_focus__workspace_focus C_matrix_negative A_matrix_negative M_matrix_negative N_matrix_negative rows j ltac:(lia) ltac:(lia))).
 unfold simplex_deduction_coef_address in *.
 replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring.
 split_pure_spatial; [sepcon_right_assoc;cancel;reflexivity | split_pures;dump_pre_spatial;auto].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_22_matrix_normal : simplex_deduction_entail_wit_22_matrix_normal.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 pose proof (PreH15 rows ltac:(lia)) as Hrow.
 pose proof (PreH16 rows j ltac:(lia)) as Hcell.
 assert (HP:In (simplex_deduction_coef_address p) PS_matrix_normal) by (subst p;tauto).
 assert (HI:In (PV_matrix_normal(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_matrix_normal) by (subst p;tauto).
 assert (HV:IV_matrix_normal(PV_matrix_normal(simplex_deduction_coef_address p)+j*sizeof(INT))=Znth(rows*9+j) A_matrix_normal 0) by (subst p;tauto).
 unfold simplex_deduction_ptrs,simplex_deduction_ints,
 simplex_deduction_ptrs_without,simplex_deduction_ints_without.
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Ptr |-> (PV_matrix_normal x)) PS_matrix_normal (simplex_deduction_coef_address p) PreH13 HP)).
 sep_apply_l_atomic (proj1(deduction_support_remove (fun x=>x # Int |-> (IV_matrix_normal x)) IS_matrix_normal (PV_matrix_normal(simplex_deduction_coef_address p)+j*sizeof(INT)) PreH14 HI)).
 sep_apply_l_atomic (proj1(workspace_focus__workspace_focus C_matrix_normal A_matrix_normal M_matrix_normal N_matrix_normal rows j ltac:(lia) ltac:(lia))).
 unfold simplex_deduction_coef_address in *.
 replace (sizeof(INT)*9) with (9*sizeof(INT)) by ring.
 split_pure_spatial; [sepcon_right_assoc;cancel;reflexivity | split_pures;dump_pre_spatial;auto].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_23_matrix_normal_split_goal_1 : simplex_deduction_entail_wit_23_matrix_normal_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_23_matrix_normal_split_goal_2 : simplex_deduction_entail_wit_23_matrix_normal_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_23_matrix_normal_split_goal_spatial : simplex_deduction_entail_wit_23_matrix_normal_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 assert (HP:In (simplex_deduction_coef_address p) PS_matrix_normal).
 { match goal with E:p=Znth rows P_matrix_normal 0 |- _ => rewrite E end.
    match goal with H:forall i:Z, 0<=i /\ i<M_matrix_normal -> _ |- _ => pose proof(H rows ltac:(lia)) as HH; tauto end. }
 assert (HI:In (PV_matrix_normal(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_matrix_normal).
 { match goal with E:p=Znth rows P_matrix_normal 0 |- _ => rewrite E end.
    match goal with H:forall i h:Z, _ -> In _ IS_matrix_normal /\ _ |- _ => pose proof(H rows j ltac:(lia)) as HH; tauto end. }
 unfold simplex_deduction_ptrs_without,simplex_deduction_ints_without,
 simplex_deduction_ptrs,simplex_deduction_ints.
 rewrite (deduction_support_remove (fun z=>z # Ptr |-> (PV_matrix_normal z)) PS_matrix_normal (simplex_deduction_coef_address p) ltac:(assumption) HP).
 rewrite (deduction_support_remove (fun z=>z # Int |-> (IV_matrix_normal z)) IS_matrix_normal (PV_matrix_normal(simplex_deduction_coef_address p)+j*sizeof(INT)) ltac:(assumption) HI).
 sep_apply_r_atomic (workspace_update__workspace_update C_matrix_normal A_matrix_normal M_matrix_normal N_matrix_normal rows j ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_deduction_coef_address in *.
 match goal with H:IV_matrix_normal _ = Znth _ A_matrix_normal 0 |- _ => rewrite H end.
 replace (C_matrix_normal+rows*(9*sizeof(INT))+j*sizeof(INT)) with
 (C_matrix_normal+rows*(sizeof(INT)*9)+j*sizeof(INT)) by ring.
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_23_matrix_normal : simplex_deduction_entail_wit_23_matrix_normal.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_simplex_deduction_entail_wit_23_matrix_normal_split_goal_spatial CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_23_matrix_normal_split_goal_1 CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_23_matrix_normal_split_goal_2 CO_matrix_normal C_matrix_normal Old_matrix_normal L_matrix_normal S_matrix_normal N_matrix_normal M_matrix_normal IV_matrix_normal PV_matrix_normal IS_matrix_normal PS_matrix_normal P_matrix_normal A_matrix_normal list rows p j).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_24_matrix_negative_split_goal_1 : simplex_deduction_entail_wit_24_matrix_negative_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_24_matrix_negative_split_goal_2 : simplex_deduction_entail_wit_24_matrix_negative_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_24_matrix_negative_split_goal_spatial : simplex_deduction_entail_wit_24_matrix_negative_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 assert (HP:In (simplex_deduction_coef_address p) PS_matrix_negative).
 { match goal with E:p=Znth rows P_matrix_negative 0 |- _ => rewrite E end.
    match goal with H:forall i:Z, 0<=i /\ i<M_matrix_negative -> _ |- _ => pose proof(H rows ltac:(lia)) as HH; tauto end. }
 assert (HI:In (PV_matrix_negative(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_matrix_negative).
 { match goal with E:p=Znth rows P_matrix_negative 0 |- _ => rewrite E end.
    match goal with H:forall i h:Z, _ -> In _ IS_matrix_negative /\ _ |- _ => pose proof(H rows j ltac:(lia)) as HH; tauto end. }
 unfold simplex_deduction_ptrs_without,simplex_deduction_ints_without,
 simplex_deduction_ptrs,simplex_deduction_ints.
 rewrite (deduction_support_remove (fun z=>z # Ptr |-> (PV_matrix_negative z)) PS_matrix_negative (simplex_deduction_coef_address p) ltac:(assumption) HP).
 rewrite (deduction_support_remove (fun z=>z # Int |-> (IV_matrix_negative z)) IS_matrix_negative (PV_matrix_negative(simplex_deduction_coef_address p)+j*sizeof(INT)) ltac:(assumption) HI).
 sep_apply_r_atomic (workspace_update__workspace_update C_matrix_negative A_matrix_negative M_matrix_negative N_matrix_negative rows j ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_deduction_coef_address in *.
 match goal with H:IV_matrix_negative _ = Znth _ A_matrix_negative 0 |- _ => rewrite H end.
 replace (C_matrix_negative+rows*(9*sizeof(INT))+j*sizeof(INT)) with
 (C_matrix_negative+rows*(sizeof(INT)*9)+j*sizeof(INT)) by ring.
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_24_matrix_negative : simplex_deduction_entail_wit_24_matrix_negative.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_simplex_deduction_entail_wit_24_matrix_negative_split_goal_spatial CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_24_matrix_negative_split_goal_1 CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_24_matrix_negative_split_goal_2 CO_matrix_negative C_matrix_negative Old_matrix_negative L_matrix_negative S_matrix_negative N_matrix_negative M_matrix_negative IV_matrix_negative PV_matrix_negative IS_matrix_negative PS_matrix_negative P_matrix_negative A_matrix_negative list rows p j).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_25_complete_min : simplex_deduction_entail_wit_25_complete_min.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 assert (HP:In (simplex_deduction_coef_address p) PS_complete_min).
 { match goal with E:p=Znth rows P_complete_min 0 |- _ => rewrite E end.
    match goal with H:forall i:Z, 0<=i /\ i<M_complete_min -> _ |- _ => pose proof(H rows ltac:(lia)) as HH; tauto end. }
 assert (HI:In (PV_complete_min(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_complete_min).
 { match goal with E:p=Znth rows P_complete_min 0 |- _ => rewrite E end.
    match goal with H:forall i h:Z, _ -> In _ IS_complete_min /\ _ |- _ => pose proof(H rows j ltac:(lia)) as HH; tauto end. }
 Exists y_2 x_2.
 split_pure_spatial.
 2: { split_pures; dump_pre_spatial; first [assumption | lia | eauto]. }
 unfold simplex_deduction_ptrs_without,simplex_deduction_ints_without,
 simplex_deduction_ptrs,simplex_deduction_ints.
 rewrite (deduction_support_remove (fun z=>z # Ptr |-> (PV_complete_min z)) PS_complete_min (simplex_deduction_coef_address p) ltac:(assumption) HP).
 rewrite (deduction_support_remove (fun z=>z # Int |-> (IV_complete_min z)) IS_complete_min (PV_complete_min(simplex_deduction_coef_address p)+j*sizeof(INT)) ltac:(assumption) HI).
 sep_apply_r_atomic (workspace_update__workspace_update C_complete_min A_complete_min M_complete_min N_complete_min rows j ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_deduction_coef_address in *.
 match goal with H:IV_complete_min _ = Znth _ A_complete_min 0 |- _ => rewrite H end.
 replace (C_complete_min+rows*(9*sizeof(INT))+j*sizeof(INT)) with
 (C_complete_min+rows*(sizeof(INT)*9)+j*sizeof(INT)) by ring.
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_1 : simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_2 : simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_spatial : simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 assert (HP:In (simplex_deduction_coef_address p) PS_bounded_prefix_reject).
 { match goal with E:p=Znth rows P_bounded_prefix_reject 0 |- _ => rewrite E end.
    match goal with H:forall i:Z, 0<=i /\ i<M_bounded_prefix_reject -> _ |- _ => pose proof(H rows ltac:(lia)) as HH; tauto end. }
 assert (HI:In (PV_bounded_prefix_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_bounded_prefix_reject).
 { match goal with E:p=Znth rows P_bounded_prefix_reject 0 |- _ => rewrite E end.
    match goal with H:forall i h:Z, _ -> In _ IS_bounded_prefix_reject /\ _ |- _ => pose proof(H rows j ltac:(lia)) as HH; tauto end. }
 unfold simplex_deduction_ptrs_without,simplex_deduction_ints_without,
 simplex_deduction_ptrs,simplex_deduction_ints.
 rewrite (deduction_support_remove (fun z=>z # Ptr |-> (PV_bounded_prefix_reject z)) PS_bounded_prefix_reject (simplex_deduction_coef_address p) ltac:(assumption) HP).
 rewrite (deduction_support_remove (fun z=>z # Int |-> (IV_bounded_prefix_reject z)) IS_bounded_prefix_reject (PV_bounded_prefix_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) ltac:(assumption) HI).
 sep_apply_r_atomic (workspace_update__workspace_update C_bounded_prefix_reject A_bounded_prefix_reject M_bounded_prefix_reject N_bounded_prefix_reject rows j ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_deduction_coef_address in *.
 match goal with H:IV_bounded_prefix_reject _ = Znth _ A_bounded_prefix_reject 0 |- _ => rewrite H end.
 replace (C_bounded_prefix_reject+rows*(9*sizeof(INT))+j*sizeof(INT)) with
 (C_bounded_prefix_reject+rows*(sizeof(INT)*9)+j*sizeof(INT)) by ring.
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject : simplex_deduction_entail_wit_26_bounded_prefix_reject.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_spatial C_bounded_prefix_reject L_bounded_prefix_reject N_bounded_prefix_reject M_bounded_prefix_reject IV_bounded_prefix_reject PV_bounded_prefix_reject IS_bounded_prefix_reject PS_bounded_prefix_reject P_bounded_prefix_reject A_bounded_prefix_reject list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_1 C_bounded_prefix_reject L_bounded_prefix_reject N_bounded_prefix_reject M_bounded_prefix_reject IV_bounded_prefix_reject PV_bounded_prefix_reject IS_bounded_prefix_reject PS_bounded_prefix_reject P_bounded_prefix_reject A_bounded_prefix_reject list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_26_bounded_prefix_reject_split_goal_2 C_bounded_prefix_reject L_bounded_prefix_reject N_bounded_prefix_reject M_bounded_prefix_reject IV_bounded_prefix_reject PV_bounded_prefix_reject IS_bounded_prefix_reject PS_bounded_prefix_reject P_bounded_prefix_reject A_bounded_prefix_reject list rows p j).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_1 : simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_2 : simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; eauto).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_spatial : simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 assert (HP:In (simplex_deduction_coef_address p) PS_nullcoef_reject).
 { match goal with E:p=Znth rows P_nullcoef_reject 0 |- _ => rewrite E end.
    match goal with H:forall i:Z, 0<=i /\ i<M_nullcoef_reject -> _ |- _ => pose proof(H rows ltac:(lia)) as HH; tauto end. }
 assert (HI:In (PV_nullcoef_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) IS_nullcoef_reject).
 { match goal with E:p=Znth rows P_nullcoef_reject 0 |- _ => rewrite E end.
    match goal with H:forall i h:Z, _ -> In _ IS_nullcoef_reject /\ _ |- _ => pose proof(H rows j ltac:(lia)) as HH; tauto end. }
 unfold simplex_deduction_ptrs_without,simplex_deduction_ints_without,
 simplex_deduction_ptrs,simplex_deduction_ints.
 rewrite (deduction_support_remove (fun z=>z # Ptr |-> (PV_nullcoef_reject z)) PS_nullcoef_reject (simplex_deduction_coef_address p) ltac:(assumption) HP).
 rewrite (deduction_support_remove (fun z=>z # Int |-> (IV_nullcoef_reject z)) IS_nullcoef_reject (PV_nullcoef_reject(simplex_deduction_coef_address p)+j*sizeof(INT)) ltac:(assumption) HI).
 sep_apply_r_atomic (workspace_update__workspace_update C_nullcoef_reject A_nullcoef_reject M_nullcoef_reject N_nullcoef_reject rows j ltac:(lia) ltac:(lia) ltac:(lia)).
 unfold simplex_deduction_coef_address in *.
 match goal with H:IV_nullcoef_reject _ = Znth _ A_nullcoef_reject 0 |- _ => rewrite H end.
 replace (C_nullcoef_reject+rows*(9*sizeof(INT))+j*sizeof(INT)) with
 (C_nullcoef_reject+rows*(sizeof(INT)*9)+j*sizeof(INT)) by ring.
 sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_27_nullcoef_reject : simplex_deduction_entail_wit_27_nullcoef_reject.
Proof.
aggressive_pre_process.
Goal_apply (proof_of_simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_spatial C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_1 C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p j).
Goal_apply (proof_of_simplex_deduction_entail_wit_27_nullcoef_reject_split_goal_2 C_nullcoef_reject L_nullcoef_reject N_nullcoef_reject M_nullcoef_reject IV_nullcoef_reject PV_nullcoef_reject IS_nullcoef_reject PS_nullcoef_reject P_nullcoef_reject A_nullcoef_reject list rows p j).
Qed.

Lemma proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_1 : simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_2 : simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_3 : simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_spatial : simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EJ:j=N_nullcoef_reject+1) by lia. subst j.
  rewrite (workspace_row_close__row_advance C_nullcoef_reject A_nullcoef_reject M_nullcoef_reject N_nullcoef_reject rows ltac:(lia) ltac:(lia)).
  pose proof (PreH15 rows ltac:(lia)) as Hnode.
  destruct Hnode as [[[[Hnz Hcoef] Hnext] Hcnz] Hval].
  rewrite <- PreH23 in Hnext,Hval.
  unfold simplex_deduction_ptrs, simplex_deduction_ptrs_without.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_nullcoef_reject x)) PS_nullcoef_reject (simplex_deduction_next_address p) PreH13 Hnext).
  unfold simplex_deduction_next_address in Hval |- *.
  rewrite Hval. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_28_nullcoef_reject : simplex_deduction_entail_wit_28_nullcoef_reject.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_28_nullcoef_reject_split_goal_3.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_1 : simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_2 : simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_3 : simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_spatial : simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EJ:j=N_bounded_prefix_reject+1) by lia. subst j.
  rewrite (workspace_row_close__row_advance C_bounded_prefix_reject A_bounded_prefix_reject M_bounded_prefix_reject N_bounded_prefix_reject rows ltac:(lia) ltac:(lia)).
  pose proof (PreH15 rows ltac:(lia)) as Hnode.
  destruct Hnode as [[[[Hnz Hcoef] Hnext] Hcnz] Hval].
  rewrite <- PreH21 in Hnext,Hval.
  unfold simplex_deduction_ptrs, simplex_deduction_ptrs_without.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_bounded_prefix_reject x)) PS_bounded_prefix_reject (simplex_deduction_next_address p) PreH13 Hnext).
  unfold simplex_deduction_next_address in Hval |- *.
  rewrite Hval. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject : simplex_deduction_entail_wit_29_bounded_prefix_reject.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_29_bounded_prefix_reject_split_goal_3.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_30_complete_min : simplex_deduction_entail_wit_30_complete_min.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists y_2 x_2.
  split_pure_spatial.
  - assert (EJ:j=N_complete_min+1) by lia. subst j.
  rewrite (workspace_row_close__row_advance C_complete_min A_complete_min M_complete_min N_complete_min rows ltac:(lia) ltac:(lia)).
  pose proof (PreH15 rows ltac:(lia)) as Hnode.
  destruct Hnode as [[[[Hnz Hcoef] Hnext] Hcnz] Hval].
  rewrite <- PreH25 in Hnext,Hval.
  unfold simplex_deduction_ptrs, simplex_deduction_ptrs_without.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_complete_min x)) PS_complete_min (simplex_deduction_next_address p) PreH13 Hnext).
  unfold simplex_deduction_next_address in Hval |- *.
  rewrite Hval. cancel; reflexivity.
  - split_pures; dump_pre_spatial; try replace (rows+1-1) with rows by lia; first [assumption | lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_1 : simplex_deduction_entail_wit_31_matrix_negative_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_2 : simplex_deduction_entail_wit_31_matrix_negative_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_3 : simplex_deduction_entail_wit_31_matrix_negative_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_spatial : simplex_deduction_entail_wit_31_matrix_negative_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EJ:j=N_matrix_negative+1) by lia. subst j.
  rewrite (workspace_row_close__row_advance C_matrix_negative A_matrix_negative M_matrix_negative N_matrix_negative rows ltac:(lia) ltac:(lia)).
  pose proof (PreH15 rows ltac:(lia)) as Hnode.
  destruct Hnode as [[[[Hnz Hcoef] Hnext] Hcnz] Hval].
  rewrite <- PreH23 in Hnext,Hval.
  unfold simplex_deduction_ptrs, simplex_deduction_ptrs_without.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_matrix_negative x)) PS_matrix_negative (simplex_deduction_next_address p) PreH13 Hnext).
  unfold simplex_deduction_next_address in Hval |- *.
  rewrite Hval. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_31_matrix_negative : simplex_deduction_entail_wit_31_matrix_negative.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_31_matrix_negative_split_goal_3.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_1 : simplex_deduction_entail_wit_32_matrix_normal_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_2 : simplex_deduction_entail_wit_32_matrix_normal_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_3 : simplex_deduction_entail_wit_32_matrix_normal_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; try replace (rows+1-1) with rows by lia; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_spatial : simplex_deduction_entail_wit_32_matrix_normal_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (EJ:j=N_matrix_normal+1) by lia. subst j.
  rewrite (workspace_row_close__row_advance C_matrix_normal A_matrix_normal M_matrix_normal N_matrix_normal rows ltac:(lia) ltac:(lia)).
  pose proof (PreH15 rows ltac:(lia)) as Hnode.
  destruct Hnode as [[[[Hnz Hcoef] Hnext] Hcnz] Hval].
  rewrite <- PreH23 in Hnext,Hval.
  unfold simplex_deduction_ptrs, simplex_deduction_ptrs_without.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_matrix_normal x)) PS_matrix_normal (simplex_deduction_next_address p) PreH13 Hnext).
  unfold simplex_deduction_next_address in Hval |- *.
  rewrite Hval. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_32_matrix_normal : simplex_deduction_entail_wit_32_matrix_normal.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_32_matrix_normal_split_goal_3.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_33_matrix_normal : simplex_deduction_entail_wit_33_matrix_normal.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HN := PreH14 (rows-1) ltac:(lia)).
  destruct HN as [[[[Hnode Hcoef] Hnext] Hnon] Hvalue].
  rewrite <- PreH22 in Hnext,Hvalue.
  replace (rows-1+1) with rows in Hvalue by lia.
  unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_matrix_normal x)) PS_matrix_normal (simplex_deduction_next_address p) PreH12 Hnext).
  unfold simplex_deduction_next_address in Hvalue |- *.
  rewrite Hvalue.
  sep_apply_l_atomic (store_int_undef_store_int (&("j")) (N_matrix_normal+1)).
  destruct (Z.eq_dec rows M_matrix_normal) as [E|E].
  - subst rows. Left.
    rewrite deduction_workspace_complete.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; auto; lia].
  - assert (Hne := PreH14 rows ltac:(lia)).
    destruct Hne as [[[[Hne ?] ?] ?] ?].
    Right. Exists rows.
    rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_matrix_normal x)) PS_matrix_normal (simplex_deduction_next_address p) PreH12 Hnext).
    unfold simplex_deduction_next_address. rewrite Hvalue.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_34_matrix_negative : simplex_deduction_entail_wit_34_matrix_negative.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HN := PreH14 (rows-1) ltac:(lia)).
  destruct HN as [[[[Hnode Hcoef] Hnext] Hnon] Hvalue].
  rewrite <- PreH22 in Hnext,Hvalue.
  replace (rows-1+1) with rows in Hvalue by lia.
  unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_matrix_negative x)) PS_matrix_negative (simplex_deduction_next_address p) PreH12 Hnext).
  unfold simplex_deduction_next_address in Hvalue |- *.
  rewrite Hvalue.
  sep_apply_l_atomic (store_int_undef_store_int (&("j")) (N_matrix_negative+1)).
  destruct (Z.eq_dec rows M_matrix_negative) as [E|E].
  - subst rows. Left.
    rewrite deduction_workspace_complete.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; auto; lia].
  - assert (Hne := PreH14 rows ltac:(lia)).
    destruct Hne as [[[[Hne ?] ?] ?] ?].
    Right. Exists rows.
    rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_matrix_negative x)) PS_matrix_negative (simplex_deduction_next_address p) PreH12 Hnext).
    unfold simplex_deduction_next_address. rewrite Hvalue.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_35_complete_min : simplex_deduction_entail_wit_35_complete_min.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HN := PreH14 (rows-1) ltac:(lia)).
  destruct HN as [[[[Hnode Hcoef] Hnext] Hnon] Hvalue].
  rewrite <- PreH24 in Hnext,Hvalue.
  replace (rows-1+1) with rows in Hvalue by lia.
  unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
  unfold simplex_deduction_next_address in Hvalue |- *.
  sep_apply_l_atomic (store_int_undef_store_int (&("j")) (N_complete_min+1)).
  destruct (Z.eq_dec rows M_complete_min) as [E|E].
  - subst rows. Left.
    Exists y_2 x_2.
    rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_complete_min x)) PS_complete_min (simplex_deduction_next_address p) PreH12 Hnext).
    unfold simplex_deduction_next_address. rewrite Hvalue.
    rewrite deduction_workspace_complete.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; auto; lia].
  - assert (Hne := PreH14 rows ltac:(lia)).
    destruct Hne as [[[[Hne ?] ?] ?] ?].
    Right. Exists rows.
    Exists y_2 x_2.
    rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_complete_min x)) PS_complete_min (simplex_deduction_next_address p) PreH12 Hnext).
    unfold simplex_deduction_next_address. rewrite Hvalue.
    split_pure_spatial; [sepcon_right_assoc; cancel; reflexivity | split_pures; dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_1 : simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_2 : simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_3 : simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (Z.eq_dec rows M_bounded_prefix_reject) as [E|E].
  - subst rows. assumption.
  - pose proof (PreH14 rows ltac:(lia)) as H. tauto.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_spatial : simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH14 (rows-1) ltac:(lia)) as HN.
  destruct HN as [[[[Hnode Hcoef] Hnext] Hnon] Hvalue].
  rewrite <- PreH20 in Hnext,Hvalue.
  replace (rows-1+1) with rows in Hvalue by lia.
  unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_bounded_prefix_reject x)) PS_bounded_prefix_reject (simplex_deduction_next_address p) PreH12 Hnext).
  unfold simplex_deduction_next_address in Hvalue |- *.
  rewrite Hvalue. sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject : simplex_deduction_entail_wit_36_bounded_prefix_reject.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_36_bounded_prefix_reject_split_goal_3.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_1 : simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_2 : simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: dump_pre_spatial; assumption.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_3 : simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  destruct (Z.eq_dec rows M_nullcoef_reject) as [E|E].
  - subst rows. assumption.
  - pose proof (PreH14 rows ltac:(lia)) as H. tauto.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_spatial : simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH14 (rows-1) ltac:(lia)) as HN.
  destruct HN as [[[[Hnode Hcoef] Hnext] Hnon] Hvalue].
  rewrite <- PreH22 in Hnext,Hvalue.
  replace (rows-1+1) with rows in Hvalue by lia.
  unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
  rewrite (deduction_support_remove (fun x => x # Ptr |-> (PV_nullcoef_reject x)) PS_nullcoef_reject (simplex_deduction_next_address p) PreH12 Hnext).
  unfold simplex_deduction_next_address in Hvalue |- *.
  rewrite Hvalue. sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_entail_wit_37_nullcoef_reject : simplex_deduction_entail_wit_37_nullcoef_reject.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_1.
  - Goal_apply proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_2.
  - Goal_apply proof_of_simplex_deduction_entail_wit_37_nullcoef_reject_split_goal_3.
Qed.

Lemma proof_of_simplex_deduction_return_wit_2_zero_negative_split_goal_1 : simplex_deduction_return_wit_2_zero_negative_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst M_zero_negative.
assert (HA: A_zero_negative = nil).
{ destruct A_zero_negative as [|a xs]; [reflexivity|]. rewrite Zlength_cons in PreH12. pose proof (Zlength_nonneg xs). lia. }
subst A_zero_negative.
all: try dump_pre_spatial; subst retval; cbn [Z.add] in *; tauto.
Qed.

Lemma proof_of_simplex_deduction_return_wit_2_zero_negative_split_goal_spatial : simplex_deduction_return_wit_2_zero_negative_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst M_zero_negative.
assert (HA: A_zero_negative = nil).
{ destruct A_zero_negative as [|a xs]; [reflexivity|]. rewrite Zlength_cons in PreH12. pose proof (Zlength_nonneg xs). lia. }
subst A_zero_negative.
cbn [Z.add]. sepcon_right_assoc. cancel; reflexivity.
Qed.

Lemma proof_of_simplex_deduction_return_wit_2_zero_negative : simplex_deduction_return_wit_2_zero_negative.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_return_wit_2_zero_negative_split_goal_spatial C_zero_negative Old_zero_negative L_zero_negative S_zero_negative N_zero_negative M_zero_negative IV_zero_negative PV_zero_negative IS_zero_negative PS_zero_negative P_zero_negative A_zero_negative list p retval).
- Goal_apply (proof_of_simplex_deduction_return_wit_2_zero_negative_split_goal_1 C_zero_negative Old_zero_negative L_zero_negative S_zero_negative N_zero_negative M_zero_negative IV_zero_negative PV_zero_negative IS_zero_negative PS_zero_negative P_zero_negative A_zero_negative list p retval).
Qed.

Lemma proof_of_simplex_deduction_return_wit_3_zero_normal_split_goal_1 : simplex_deduction_return_wit_3_zero_normal_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: unfold simplex_init_return in *; lia.
Qed.

Lemma proof_of_simplex_deduction_return_wit_3_zero_normal : simplex_deduction_return_wit_3_zero_normal.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_return_wit_3_zero_normal_split_goal_1 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
Qed.

Lemma proof_of_simplex_deduction_return_wit_4_zero_normal_split_goal_1 : simplex_deduction_return_wit_4_zero_normal_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst M_zero_normal.
assert (HA: A_zero_normal = nil).
{ destruct A_zero_normal as [|a xs]; [reflexivity|]. rewrite Zlength_cons in PreH16. pose proof (Zlength_nonneg xs). lia. }
subst A_zero_normal.
all: try dump_pre_spatial; subst retval; cbn [Z.add] in *; tauto.
Qed.

Lemma proof_of_simplex_deduction_return_wit_4_zero_normal_split_goal_2 : simplex_deduction_return_wit_4_zero_normal_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst M_zero_normal.
assert (HA: A_zero_normal = nil).
{ destruct A_zero_normal as [|a xs]; [reflexivity|]. rewrite Zlength_cons in PreH16. pose proof (Zlength_nonneg xs). lia. }
subst A_zero_normal.
all: try dump_pre_spatial; subst retval; cbn [Z.add] in *; tauto.
Qed.

Lemma proof_of_simplex_deduction_return_wit_4_zero_normal_split_goal_3 : simplex_deduction_return_wit_4_zero_normal_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst M_zero_normal.
assert (HA: A_zero_normal = nil).
{ destruct A_zero_normal as [|a xs]; [reflexivity|]. rewrite Zlength_cons in PreH16. pose proof (Zlength_nonneg xs). lia. }
subst A_zero_normal.
all: try dump_pre_spatial; subst retval; cbn [Z.add] in *; tauto.
Qed.

Lemma proof_of_simplex_deduction_return_wit_4_zero_normal : simplex_deduction_return_wit_4_zero_normal.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_return_wit_4_zero_normal_split_goal_1 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
- Goal_apply (proof_of_simplex_deduction_return_wit_4_zero_normal_split_goal_2 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
- Goal_apply (proof_of_simplex_deduction_return_wit_4_zero_normal_split_goal_3 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
Qed.

Lemma proof_of_simplex_deduction_return_wit_5_zero_normal_split_goal_1 : simplex_deduction_return_wit_5_zero_normal_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: unfold simplex_init_return in *; lia.
Qed.

Lemma proof_of_simplex_deduction_return_wit_5_zero_normal_split_goal_2 : simplex_deduction_return_wit_5_zero_normal_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: unfold simplex_init_return in *; lia.
Qed.

Lemma proof_of_simplex_deduction_return_wit_5_zero_normal_split_goal_3 : simplex_deduction_return_wit_5_zero_normal_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
all: unfold simplex_init_return in *; lia.
Qed.

Lemma proof_of_simplex_deduction_return_wit_5_zero_normal : simplex_deduction_return_wit_5_zero_normal.
Proof.
aggressive_pre_process.
- Goal_apply (proof_of_simplex_deduction_return_wit_5_zero_normal_split_goal_1 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
- Goal_apply (proof_of_simplex_deduction_return_wit_5_zero_normal_split_goal_2 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
- Goal_apply (proof_of_simplex_deduction_return_wit_5_zero_normal_split_goal_3 L_zero_normal N_zero_normal M_zero_normal IV_zero_normal PV_zero_normal IS_zero_normal PS_zero_normal P_zero_normal A_zero_normal list p ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 retval).
Qed.

Lemma proof_of_simplex_deduction_return_wit_10_matrix_normal : simplex_deduction_return_wit_10_matrix_normal.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: assert (rows = M_matrix_normal) by lia; subst rows; congruence.
Qed.

Lemma proof_of_simplex_deduction_return_wit_11_matrix_negative_split_goal_1 : simplex_deduction_return_wit_11_matrix_negative_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: assert (rows = M_matrix_negative) by lia; subst rows; congruence.
Qed.

Lemma proof_of_simplex_deduction_return_wit_11_matrix_negative_split_goal_spatial : simplex_deduction_return_wit_11_matrix_negative_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: assert (rows = M_matrix_negative) by lia; subst rows; congruence.
Qed.

Lemma proof_of_simplex_deduction_return_wit_11_matrix_negative : simplex_deduction_return_wit_11_matrix_negative.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_return_wit_11_matrix_negative_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_return_wit_11_matrix_negative_split_goal_1.
Qed.

Lemma proof_of_simplex_deduction_return_wit_12_complete_min_split_goal_1 : simplex_deduction_return_wit_12_complete_min_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: assert (rows = M_complete_min) by lia; subst rows; congruence.
Qed.

Lemma proof_of_simplex_deduction_return_wit_12_complete_min_split_goal_spatial : simplex_deduction_return_wit_12_complete_min_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: assert (rows = M_complete_min) by lia; subst rows; congruence.
Qed.

Lemma proof_of_simplex_deduction_return_wit_12_complete_min : simplex_deduction_return_wit_12_complete_min.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_simplex_deduction_return_wit_12_complete_min_split_goal_spatial.
  - Goal_apply proof_of_simplex_deduction_return_wit_12_complete_min_split_goal_1.
Qed.

Lemma proof_of_simplex_deduction_return_wit_13_bounded_prefix_reject_split_goal_spatial : simplex_deduction_return_wit_13_bounded_prefix_reject_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (rows = M_bounded_prefix_reject) by lia.
  subst rows. cancel.
Qed.

Lemma proof_of_simplex_deduction_return_wit_13_bounded_prefix_reject : simplex_deduction_return_wit_13_bounded_prefix_reject.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_simplex_deduction_return_wit_13_bounded_prefix_reject_split_goal_spatial.
Qed.

Lemma proof_of_simplex_deduction_return_wit_14_matrix_normal : simplex_deduction_return_wit_14_matrix_normal.
Proof.
LLM_pre_process ltac:(lia || int_auto). assert (Hr : rows < M_matrix_normal) by (destruct (Z_lt_ge_dec rows M_matrix_normal); [assumption| assert (rows = M_matrix_normal) by lia; subst rows; congruence]). pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH24 in HC. assert (HF : False) by tauto. contradiction.
Qed.

Lemma proof_of_simplex_deduction_return_wit_15_matrix_negative_split_goal_1 : simplex_deduction_return_wit_15_matrix_negative_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). assert (Hr : rows < M_matrix_negative) by (destruct (Z_lt_ge_dec rows M_matrix_negative); [assumption| assert (rows = M_matrix_negative) by lia; subst rows; congruence]). pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH24 in HC. assert (HF : False) by tauto. contradiction.
Qed.

Lemma proof_of_simplex_deduction_return_wit_15_matrix_negative_split_goal_spatial : simplex_deduction_return_wit_15_matrix_negative_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto). assert (Hr : rows < M_matrix_negative) by (destruct (Z_lt_ge_dec rows M_matrix_negative); [assumption| assert (rows = M_matrix_negative) by lia; subst rows; congruence]). pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH24 in HC. assert (HF : False) by tauto. contradiction.
Qed.

Lemma proof_of_simplex_deduction_return_wit_15_matrix_negative : simplex_deduction_return_wit_15_matrix_negative.
Proof.
aggressive_pre_process. Goal_apply proof_of_simplex_deduction_return_wit_15_matrix_negative_split_goal_spatial. Goal_apply proof_of_simplex_deduction_return_wit_15_matrix_negative_split_goal_1.
Qed.

Lemma proof_of_simplex_deduction_return_wit_16_complete_min_split_goal_1 : simplex_deduction_return_wit_16_complete_min_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). assert (Hr : rows < M_complete_min) by (destruct (Z_lt_ge_dec rows M_complete_min); [assumption| assert (rows = M_complete_min) by lia; subst rows; congruence]). pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH26 in HC. assert (HF : False) by tauto. contradiction.
Qed.

Lemma proof_of_simplex_deduction_return_wit_16_complete_min_split_goal_spatial : simplex_deduction_return_wit_16_complete_min_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto). assert (Hr : rows < M_complete_min) by (destruct (Z_lt_ge_dec rows M_complete_min); [assumption| assert (rows = M_complete_min) by lia; subst rows; congruence]). pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH26 in HC. assert (HF : False) by tauto. contradiction.
Qed.

Lemma proof_of_simplex_deduction_return_wit_16_complete_min : simplex_deduction_return_wit_16_complete_min.
Proof.
aggressive_pre_process. Goal_apply proof_of_simplex_deduction_return_wit_16_complete_min_split_goal_spatial. Goal_apply proof_of_simplex_deduction_return_wit_16_complete_min_split_goal_1.
Qed.

Lemma proof_of_simplex_deduction_return_wit_17_bounded_prefix_reject_split_goal_spatial : simplex_deduction_return_wit_17_bounded_prefix_reject_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto). pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH22 in HC. assert (HF : False) by tauto. contradiction.
Qed.

Lemma proof_of_simplex_deduction_return_wit_17_bounded_prefix_reject : simplex_deduction_return_wit_17_bounded_prefix_reject.
Proof.
aggressive_pre_process. Goal_apply proof_of_simplex_deduction_return_wit_17_bounded_prefix_reject_split_goal_spatial.
Qed.

Lemma proof_of_simplex_deduction_return_wit_18_nullcoef_reject_split_goal_spatial : simplex_deduction_return_wit_18_nullcoef_reject_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto). assert (HE : rows = M_nullcoef_reject).
{ destruct (Z_lt_ge_dec rows M_nullcoef_reject) as [HL|HL]; [|lia].
pose proof (PreH16 rows ltac:(lia)) as HC. rewrite <- PreH24 in HC. tauto. }
subst rows.
assert (HI : In (simplex_deduction_coef_address p) PS_nullcoef_reject) by (rewrite PreH24; exact PreH20).
unfold simplex_deduction_ptrs_without, simplex_deduction_ptrs.
rewrite (deduction_support_remove (fun q => q # Ptr |-> (PV_nullcoef_reject q)) PS_nullcoef_reject (simplex_deduction_coef_address p) PreH14 HI).
unfold simplex_deduction_coef_address. sepcon_right_assoc. cancel. reflexivity.

Qed.

Lemma proof_of_simplex_deduction_return_wit_18_nullcoef_reject : simplex_deduction_return_wit_18_nullcoef_reject.
Proof.
aggressive_pre_process. Goal_apply proof_of_simplex_deduction_return_wit_18_nullcoef_reject_split_goal_spatial.
Qed.

Lemma proof_of_simplex_deduction_partial_solve_wit_1_complete_min_pure : simplex_deduction_partial_solve_wit_1_complete_min_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists y_2 x_2.
  split_pures; dump_pre_spatial; auto; try lia.
Qed.

