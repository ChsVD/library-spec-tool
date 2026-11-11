Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_verify_dgst_goal.
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_verify_dgst_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope sac.

Lemma proof_of_sm2_verify_dgst_return_wit_1_split_goal_1 : sm2_verify_dgst_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_1_split_goal_spatial : sm2_verify_dgst_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_1 : sm2_verify_dgst_return_wit_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - apply
      (sm2_verify_dgst_return_resources_fold
        pubkey_pre dgst_pre signature_pre SigS_verifies SigR_verifies
        P_verifies DigestBytes_verifies xs ys zs); assumption.
  - unfold store_fn, store_mod.
    Intros_p Hsrange.
    split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    repeat split; try lia; try assumption.
    exists RX, RY.
    split; [exact PreH10 |].
    rewrite Z.add_mod by (pose proof sm2_n_bounds; lia).
    symmetry; exact PreH4.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_2_split_goal_1 : sm2_verify_dgst_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_2_split_goal_spatial : sm2_verify_dgst_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_2 : sm2_verify_dgst_return_wit_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - apply
      (sm2_verify_dgst_return_resources_fold
        pubkey_pre dgst_pre signature_pre SigS_verifies SigR_verifies
        P_verifies DigestBytes_verifies xs ys zs); assumption.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    cbn zeta.
    intros [_ [_ [_ [_ [VX [VY [HV Hresult]]]]]]].
    destruct (afpoint_represents_functional _ _ _ _ _ PreH10 HV)
      as [HX _].
    subst VX.
    apply PreH4.
    rewrite Hresult.
    rewrite <- Z.add_mod by (pose proof sm2_n_bounds; lia).
    reflexivity.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_3_split_goal_1 : sm2_verify_dgst_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_3_split_goal_spatial : sm2_verify_dgst_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_3 : sm2_verify_dgst_return_wit_3.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - apply
      (sm2_verify_dgst_checked_return_resources_fold
        pubkey_pre dgst_pre signature_pre SigS_verifies SigR_verifies
        P_verifies DigestBytes_verifies xs ys zs); assumption.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    cbn zeta.
    intros [_ [_ [_ [Hresult _]]]].
    contradiction.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_4_split_goal_1 : sm2_verify_dgst_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_4_split_goal_spatial : sm2_verify_dgst_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_4 : sm2_verify_dgst_return_wit_4.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - unfold store_fn, store_mod.
    Intros_p Hranges.
    Intros_p Hsranges.
    unfold store_sm2_signature, store_u256,
      store_sm2_verify_dgst_globals, store_afpoint.
    Exists x y.
    split_pure_spatial.
    + repeat rewrite Z.mul_0_l, Z.add_0_r.
      cancel.
      sep_apply_l_atomic
        (jpoint_zero_arrays_fold xs ys zs PreH44 PreH39 PreH34).
      cancel.
    + dump_pre_spatial.
      exact PreH33.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    cbn zeta.
    intros [_ [_ [Ht _]]].
    contradiction.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_5_split_goal_1 : sm2_verify_dgst_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_5_split_goal_2 : sm2_verify_dgst_return_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_5_split_goal_spatial : sm2_verify_dgst_return_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_5 : sm2_verify_dgst_return_wit_5.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - apply
      (sm2_verify_dgst_early_return_resources_fold
        pubkey_pre dgst_pre signature_pre SigS_verifies SigR_verifies
        P_verifies DigestBytes_verifies xs ys zs x y); assumption.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    intros [Hr [Hs _]].
    rewrite u64_list_value_four in PreH5.
    destruct sm2_n_limbs_exact as [_ [_ [_ [_ HN]]]].
    lia.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_6_split_goal_1 : sm2_verify_dgst_return_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_6_split_goal_2 : sm2_verify_dgst_return_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_6_split_goal_spatial : sm2_verify_dgst_return_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_6 : sm2_verify_dgst_return_wit_6.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - assert (HN :
      u64_list_value
        (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) =
      SM2_N_Z).
    {
      rewrite u64_list_value_four.
      destruct sm2_n_limbs_exact as [_ [_ [_ [_ HN]]]].
      symmetry; exact HN.
    }
    rewrite HN.
    unfold store_sm2_signature, store_sm2_verify_dgst_globals,
      store_sm2_n, store_u256, store_afpoint.
    Exists x y.
    split_pure_spatial.
    + rewrite <- (global_u32_v_addr_eq "SM2_N").
      sep_apply_l_atomic
        (jpoint_zero_arrays_fold xs ys zs PreH23 PreH18 PreH13).
      cancel.
    + dump_pre_spatial.
      exact PreH12.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    intros [Hr [Hs _]].
    rewrite u64_list_value_four in PreH5.
    destruct sm2_n_limbs_exact as [_ [_ [_ [_ HN]]]].
    lia.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_7_split_goal_1 : sm2_verify_dgst_return_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_7_split_goal_2 : sm2_verify_dgst_return_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_7_split_goal_spatial : sm2_verify_dgst_return_wit_7_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_7 : sm2_verify_dgst_return_wit_7.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - assert (HN :
      u64_list_value
        (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) =
      SM2_N_Z).
    {
      rewrite u64_list_value_four.
      destruct sm2_n_limbs_exact as [_ [_ [_ [_ HN]]]].
      symmetry; exact HN.
    }
    rewrite HN.
    unfold store_sm2_signature, store_sm2_verify_dgst_globals,
      store_sm2_n, store_u256, store_afpoint.
    Exists x y.
    split_pure_spatial.
    + rewrite <- (global_u32_v_addr_eq "SM2_N").
      sep_apply_l_atomic
        (jpoint_zero_arrays_fold xs ys zs PreH28 PreH23 PreH18).
      cancel.
    + dump_pre_spatial.
      exact PreH17.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    intros [Hr [Hs _]].
    lia.
Qed.

Lemma proof_of_sm2_verify_dgst_return_wit_8_split_goal_1 : sm2_verify_dgst_return_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_8_split_goal_2 : sm2_verify_dgst_return_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_8_split_goal_spatial : sm2_verify_dgst_return_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_return_wit_8 : sm2_verify_dgst_return_wit_8.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pure_spatial.
  - apply
      (sm2_verify_dgst_early_return_resources_fold
        pubkey_pre dgst_pre signature_pre SigS_verifies SigR_verifies
        P_verifies DigestBytes_verifies xs ys zs x y); assumption.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    unfold sm2_signature_verifies.
    intros [Hr [Hs _]].
    lia.
Qed.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_1 : sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_2 : sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_3 : sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_4 : sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_5 : sm2_verify_dgst_partial_solve_wit_11_pure_split_goal_5.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_11_pure : sm2_verify_dgst_partial_solve_wit_11_pure.
Proof.
  unfold sm2_verify_dgst_partial_solve_wit_11_pure.
  right; intros.
  assert (HN :
    u64_list_value
      (SM2_N0_Z :: SM2_N1_Z :: SM2_N2_Z :: SM2_N3_Z :: nil) =
    SM2_N_Z) by
    (rewrite u64_list_value_four;
     destruct sm2_n_limbs_exact as [_ [_ [_ [_ HN]]]];
     symmetry; exact HN).
  rewrite HN in PreH10, PreH20.
  prop_apply_p
    (store_u256_value_range
      (&(signature_pre # "SM2SIG" ->ₛ "s")) SigS_verifies).
  Intros_p Hsrange.
  prop_apply_p
    (store_u256_value_range
      (&(signature_pre # "SM2SIG" ->ₛ "r")) SigR_verifies).
  Intros_p Hrrange.
  split_pures;
  dump_pre_spatial;
  first [lia | exact HN].
Qed.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_18_pure_split_goal_1 : sm2_verify_dgst_partial_solve_wit_18_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_sm2_verify_dgst_partial_solve_wit_18_pure : sm2_verify_dgst_partial_solve_wit_18_pure.
Proof.
  LLM_pre_process ltac:(reflexivity).
  split_pures.
  all: dump_pre_spatial.
  all: try reflexivity.
  rewrite (global_u32_v_addr_eq "t").
  rewrite u32_v_field_address_eq.
  rewrite Z.mul_0_l, Z.add_0_r.
  apply addr_of_LE_var_not_zero.
Qed.

Lemma proof_of_sm2_verify_dgst_derive_generated_by_verifies : sm2_verify_dgst_derive_generated_by_verifies.
Proof.
  LLM_pre_process ltac:(reflexivity).
  unfold store_sm2_public_key.
  Intros_p Hvalid.
  Exists DigestBytes_generated P_generated
    SigR_generated SigS_generated.
  apply sepcon_cancel_end.
  - split_pure_spatial.
    + sepcon_assoc_change.
      reflexivity.
    + dump_pre_spatial.
      apply valid_sm2_public_key_noninfinity.
      exact Hvalid.
  - apply_sepcon_adjoint.
    Split.
    + Intros retval.
      pose proof
        (proj1
          (sm2_signature_verifies_generated_iff
            (be_u8_list_value DigestBytes_generated)
            P_generated SigR_generated SigS_generated Hvalid)
          H2) as Hgenerated.
      destruct Hgenerated as [private_key [Hkeypair Hsignature]].
      Left.
      Exists private_key retval.
      unfold store_sm2_public_key.
      split_pure_spatial.
      * sepcon_assoc_change.
        reflexivity.
      * split_pures;
        dump_pre_spatial;
        assumption.
    + Intros retval.
      assert (Hnot_generated :
        ~ (exists private_key,
            valid_sm2_keypair private_key P_generated /\
            sm2_signature_generated
              (be_u8_list_value DigestBytes_generated)
              private_key SigR_generated SigS_generated)).
      {
        intros Hgenerated.
        apply H2.
        apply
          (proj2
            (sm2_signature_verifies_generated_iff
              (be_u8_list_value DigestBytes_generated)
              P_generated SigR_generated SigS_generated Hvalid)).
        exact Hgenerated.
      }
      Right.
      Exists retval.
      unfold store_sm2_public_key.
      split_pure_spatial.
      * sepcon_assoc_change.
        reflexivity.
      * split_pures;
        dump_pre_spatial;
        assumption.
Qed.
