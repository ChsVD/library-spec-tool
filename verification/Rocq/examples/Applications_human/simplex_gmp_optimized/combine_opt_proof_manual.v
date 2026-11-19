From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import combine_opt_goal.
From SimpleC.EE.Applications_human.simplex_gmp_optimized Require Import combine_opt_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_combine_entail_wit_1 : combine_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_Z at 2.
  Intros ptr ms mc.
  sep_apply_l_atomic (store_Z_from_fields a_pre ptr_2 size cap_2 A_non_alias PreH3 PreH2).
  destruct (Z.eq_dec ms 1) as [Hone | Hother].
  - subst ms. Right.
    assert (HM : 0 <= M_non_alias) by (unfold same_sign in *; lia).
    rewrite (Z.abs_eq M_non_alias HM).
    change (Zabs 1) with 1 in *.
    unfold mpd_store_Z_compact at 1.
    Intros data.
    assert (Hsingle : exists limb, data = limb :: nil).
    { destruct data as [|limb [|next tail]].
      - rewrite Zlength_nil in *. lia.
      - eauto.
      - repeat rewrite Zlength_cons in *.
        pose proof (Zlength_nonneg tail). lia. }
    destruct Hsingle as [limb ->].
    match goal with
    | H : list_to_Z UINT_MOD (limb :: nil) = _ /\ _ |- _ =>
        destruct H as [Hval [Hhigh Hbounds]]
    end.
    rewrite list_to_Z_single in Hval.
    subst limb.
    simpl in Hhigh, Hbounds.
    unfold mpd_store_list.
    rewrite Zlength_cons, Zlength_nil.
    change (Z.succ 0) with 1.
    Exists ptr mc 1.
    split_pure_spatial.
    + sepcon_right_assoc. cancel. reflexivity.
    + split_pures; dump_pre_spatial; try assumption; unfold UINT_MOD in *; lia.
  - Left. Exists ptr mc ms.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_combine_entail_wit_2_2_split_goal_spatial : combine_entail_wit_2_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst msize.
  assert (Hz : 1 <= M_non_alias < UINT_MOD).
  { change UINT_MOD with 4294967296. change UINT_MAX with 4294967295 in *. lia. }
  rewrite Z.abs_eq by lia.
  change (Zabs 1) with 1 in *.
  change (replace_Znth 0 M_non_alias (M_non_alias :: nil)) with (M_non_alias :: nil) in *.
  assert (Hv : 1 <= M_non_alias < UINT_MOD).
  { change UINT_MOD with 4294967296. try change UINT_MAX with 4294967295 in *. lia. }
  assert (Hdigits : list_within_bound UINT_MOD (M_non_alias :: nil)).
  { simpl. lia. }
  assert (Hcompact : is_compact_Z UINT_MOD M_non_alias 1).
  { exists (M_non_alias :: nil).
    rewrite list_to_Z_single, Zlength_cons, Zlength_nil.
    simpl. repeat split; lia. }
  sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_compact ptr 1 (M_non_alias :: nil) M_non_alias
    ltac:(reflexivity) ltac:(apply list_to_Z_single) Hdigits Hcompact).
  cancel.
Qed.

Lemma proof_of_combine_entail_wit_2_2 : combine_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_combine_entail_wit_2_2_split_goal_spatial.
Qed.

Lemma proof_of_combine_return_wit_1_split_goal_spatial : combine_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size size_2.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs A_non_alias)).
  Intros_p HA_abs.
  assert (HA : A_non_alias = 0) by lia.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs B_non_alias)).
  Intros_p HB_abs.
  assert (HB : B_non_alias = 0) by lia.
  replace (M_non_alias * A_non_alias + N_non_alias * B_non_alias)
    with 0 by (rewrite HA, HB; lia).
  cancel.
Qed.

Lemma proof_of_combine_return_wit_1 : combine_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_combine_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_combine_return_wit_2_split_goal_spatial : combine_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs A_non_alias)).
  Intros_p HA_abs.
  assert (HA : A_non_alias = 0) by lia.
  replace (M_non_alias * A_non_alias + N_non_alias * B_non_alias)
    with (N_non_alias * B_non_alias) by (rewrite HA; lia).
  cancel.
Qed.

Lemma proof_of_combine_return_wit_2 : combine_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_combine_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_combine_return_wit_3_split_goal_spatial : combine_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst M_non_alias.
  rewrite Z.mul_1_l.
  change (Zabs 1) with 1 in *.
  change (replace_Znth 0 1 (1 :: nil)) with (1 :: nil) in *.
  subst msize. change (Zabs 1) with 1 in *.
  assert (Hv : 1 <= 1 < UINT_MOD).
  { change UINT_MOD with 4294967296. try change UINT_MAX with 4294967295 in *. lia. }
  assert (Hdigits : list_within_bound UINT_MOD (1 :: nil)).
  { simpl. lia. }
  assert (Hcompact : is_compact_Z UINT_MOD 1 1).
  { exists (1 :: nil).
    rewrite list_to_Z_single, Zlength_cons, Zlength_nil.
    simpl. repeat split; lia. }
  sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_compact ptr 1 (1 :: nil) 1
    ltac:(reflexivity) ltac:(apply list_to_Z_single) Hdigits Hcompact).
  cancel.
Qed.

Lemma proof_of_combine_return_wit_3 : combine_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_combine_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_combine_return_wit_5_split_goal_spatial : combine_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size.
  change (Zabs 0) with 0 in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr_2 (Zabs B_non_alias)).
  Intros_p HBmag.
  assert (HB : B_non_alias = 0).
  { destruct (Z_le_gt_dec 0 B_non_alias).
    - rewrite Z.abs_eq in HBmag by lia. exact HBmag.
    - rewrite Z.abs_neq in HBmag by lia. lia. }
  subst B_non_alias.
  subst M_non_alias.
  rewrite Z.mul_1_l.
  rewrite Z.mul_0_r, Z.add_0_r.
  change (Zabs 1) with 1 in *.
  change (replace_Znth 0 1 (1 :: nil)) with (1 :: nil) in *.
  subst msize. change (Zabs 1) with 1 in *.
  assert (Hv : 1 <= 1 < UINT_MOD).
  { change UINT_MOD with 4294967296. try change UINT_MAX with 4294967295 in *. lia. }
  assert (Hdigits : list_within_bound UINT_MOD (1 :: nil)).
  { simpl. lia. }
  assert (Hcompact : is_compact_Z UINT_MOD 1 1).
  { exists (1 :: nil).
    rewrite list_to_Z_single, Zlength_cons, Zlength_nil.
    simpl. repeat split; lia. }
  sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_compact ptr 1 (1 :: nil) 1
    ltac:(reflexivity) ltac:(apply list_to_Z_single) Hdigits Hcompact).
  cancel.
Qed.

Lemma proof_of_combine_return_wit_5 : combine_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_combine_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_combine_return_wit_6_split_goal_spatial : combine_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst size.
  cbn [Z.abs] in *.
  prop_apply_p (mpd_store_Z_compact_zero UINT_MOD ptr (Zabs B_non_alias)).
  Intros_p HB_abs.
  assert (HB : B_non_alias = 0) by lia.
  replace (M_non_alias * A_non_alias + N_non_alias * B_non_alias)
    with (M_non_alias * A_non_alias) by (rewrite HB; lia).
  cancel.
Qed.

Lemma proof_of_combine_return_wit_6 : combine_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_combine_return_wit_6_split_goal_spatial.
Qed.

