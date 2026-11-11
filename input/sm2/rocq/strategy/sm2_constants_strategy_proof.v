Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm2_constants_strategy10_correctness : sm2_constants_strategy10.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy20_correctness : sm2_constants_strategy20.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy30_correctness : sm2_constants_strategy30.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy40_correctness : sm2_constants_strategy40.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy50_correctness : sm2_constants_strategy50.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy53_correctness : sm2_constants_strategy53.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_neg_inv_n.
  cancel.
Qed.

Lemma sm2_constants_strategy60_correctness : sm2_constants_strategy60.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy70_correctness : sm2_constants_strategy70.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy92_correctness : sm2_constants_strategy92.
Proof.
  pre_process_default.
  unfold store_sm2_p.
  rewrite <- (global_u32_v_addr_eq "SM2_P").
  pose proof sm2_p_limbs as [H0 [H1 [H2 [H3 Hrepr]]]].
  assert (Hvalue :
    u64_list_value
      (@cons Z SM2_P_LIMB_0
        (@cons Z SM2_P_LIMB_1
          (@cons Z SM2_P_LIMB_2
            (@cons Z SM2_P_LIMB_3 (@nil Z))))) = SM2_P_Z).
  {
    rewrite u64_list_value_four.
    symmetry.
    exact Hrepr.
  }
  rewrite <- Hvalue.
  apply uint64_full4_to_store_u256_limbs.
Qed.

Lemma sm2_constants_strategy93_correctness : sm2_constants_strategy93.
Proof.
  pre_process_default.
  unfold store_sm2_n.
  rewrite <- (global_u32_v_addr_eq "SM2_N").
  assert (Hvalue :
    u64_list_value
      (@cons Z SM2_N0_Z
        (@cons Z SM2_N1_Z
          (@cons Z SM2_N2_Z
            (@cons Z SM2_N3_Z (@nil Z))))) = SM2_N_Z).
  {
    rewrite u64_list_value_four.
    reflexivity.
  }
  rewrite <- Hvalue.
  apply uint64_full4_to_store_u256_limbs.
Qed.

Lemma sm2_constants_strategy11_correctness : sm2_constants_strategy11.
Proof.
  pre_process_default.
  unfold store_sm2_p.
  rewrite <- (global_u32_v_addr_eq "SM2_P").
  pose proof sm2_p_limbs as [H0 [H1 [H2 [H3 Hrepr]]]].
  apply store_u256_limbs_to_uint64_full4.
  - reflexivity.
  - unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    split; [exact H0 |].
    split; [exact H1 |].
    split; [exact H2 |].
    split; [exact H3 |].
    unfold limb_list_bounded.
    intros i Hi.
    rewrite Zlength_nil in Hi.
    lia.
  - rewrite u64_list_value_four.
    symmetry.
    exact Hrepr.
Qed.

Lemma sm2_constants_strategy21_correctness : sm2_constants_strategy21.
Proof.
  pre_process_default.
  unfold store_sm2_n.
  rewrite <- (global_u32_v_addr_eq "SM2_N").
  pose proof sm2_n_limbs_exact as [H0 [H1 [H2 [H3 Hrepr]]]].
  apply store_u256_limbs_to_uint64_full4.
  - reflexivity.
  - unfold u64_list_bounded.
    repeat rewrite limb_list_bounded_cons_iff.
    split; [exact H0 |].
    split; [exact H1 |].
    split; [exact H2 |].
    split; [exact H3 |].
    unfold limb_list_bounded.
    intros i Hi.
    rewrite Zlength_nil in Hi.
    lia.
  - rewrite u64_list_value_four.
    symmetry.
    exact Hrepr.
Qed.

Lemma sm2_constants_strategy31_correctness : sm2_constants_strategy31.
Proof.
  pre_process_default.
  unfold store_sm2_rhop, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_rhoP").
  reflexivity.
Qed.

Lemma sm2_constants_strategy41_correctness : sm2_constants_strategy41.
Proof.
  pre_process_default.
  unfold store_sm2_rhon, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_rhoN").
  reflexivity.
Qed.

Lemma sm2_constants_strategy51_correctness : sm2_constants_strategy51.
Proof. pre_process_default. Qed.

Lemma sm2_constants_strategy61_correctness : sm2_constants_strategy61.
Proof.
  pre_process_default.
  unfold store_sm2_h, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_H").
  reflexivity.
Qed.

Lemma sm2_constants_strategy71_correctness : sm2_constants_strategy71.
Proof.
  pre_process_default.
  unfold store_sm2_nh, store_fn, store_mod, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_NH").
  pose proof sm2_nh_bounds as Hbounds.
  entailer!.
Qed.

Lemma sm2_constants_strategy81_correctness : sm2_constants_strategy81.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_p, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_P").
  cancel.
Qed.

Lemma sm2_constants_strategy83_correctness : sm2_constants_strategy83.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_n, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_N").
  cancel.
Qed.

Lemma sm2_constants_strategy85_correctness : sm2_constants_strategy85.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_rhop, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_rhoP").
  cancel.
Qed.

Lemma sm2_constants_strategy87_correctness : sm2_constants_strategy87.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_rhon, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_rhoN").
  cancel.
Qed.

Lemma sm2_constants_strategy89_correctness : sm2_constants_strategy89.
Proof.
  pre_process_default.
  cancel.
  Intros_p Hx.
  subst x.
  unfold store_sm2_h, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_H").
  cancel.
Qed.

Lemma sm2_constants_strategy91_correctness : sm2_constants_strategy91.
Proof.
  unfold sm2_constants_strategy91.
  intros.
  unfold store_sm2_nh, store_fn, store_mod, store_u256.
  rewrite <- (global_u32_v_addr_eq "SM2_NH").
  TT_simpl.
  elim_emp.
  apply_sepcon_adjoint.
  Intros_p Hrange.
  Intros_p Hx.
  subst x.
  reflexivity.
Qed.
