Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sm2_representation_strategy10_correctness : sm2_representation_strategy10.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sm2_representation_strategy13_correctness : sm2_representation_strategy13.
Proof.
  pre_process_default.
  subst q.
  unfold store_u256.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma sm2_representation_strategy14_correctness : sm2_representation_strategy14.
Proof.
  pre_process_default.
  subst q.
  rewrite Z.add_0_r.
  Intros; subst.
  entailer!.
Qed.

Lemma sm2_representation_strategy20_correctness : sm2_representation_strategy20.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sm2_representation_strategy23_correctness : sm2_representation_strategy23.
Proof.
  pre_process_default.
  Intros.
  subst x.
  apply uint64_full4_to_store_u256_limbs.
Qed.

Lemma sm2_representation_strategy25_correctness : sm2_representation_strategy25.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros_p Halias.
  destruct Halias as [Halias | Halias]; subst result;
    simpl;
    sep_apply store_u256_limbs_to_undef_full;
    entailer!;
    rewrite Z.add_0_r;
    rewrite <- derivable1_wand_sepcon_adjoint;
    entailer!.
Qed.

Lemma sm2_representation_strategy24_correctness : sm2_representation_strategy24.
Proof.
  pre_process_default.
  subst q.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma sm2_representation_strategy30_correctness : sm2_representation_strategy30.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sm2_representation_strategy40_correctness : sm2_representation_strategy40.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sm2_representation_strategy46_correctness : sm2_representation_strategy46.
Proof.
  pre_process_default.
  subst q.
  unfold store_fp, store_mod, store_u256.
  Intros.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma sm2_representation_strategy47_correctness : sm2_representation_strategy47.
Proof.
  pre_process_default.
  subst q.
  unfold store_fp, store_mod.
  entailer!.
  cancel.
  pre_process_default.
  Intros_p Hxy.
  subst y.
  cancel.
Qed.

Lemma sm2_representation_strategy43_correctness : sm2_representation_strategy43.
Proof.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma sm2_representation_strategy48_correctness : sm2_representation_strategy48.
Proof.
  pre_process_default.
  subst q.
  unfold store_fn, store_mod.
  entailer!.
  cancel.
  pre_process_default.
  Intros_p Hxy.
  subst y.
  cancel.
Qed.

Lemma sm2_representation_strategy51_correctness : sm2_representation_strategy51.
Proof.
  pre_process_default.
  subst q.
  unfold store_fn, store_mod, store_u256.
  Intros.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma sm2_representation_strategy52_correctness : sm2_representation_strategy52.
Proof.
  pre_process_default.
  subst q.
  rewrite Z.mul_0_l, Z.add_0_r.
  unfold store_fn, store_mod, store_u256.
  Intros.
  sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma sm2_representation_strategy11_correctness : sm2_representation_strategy11.
Proof.
  pre_process_default.
Qed.

Lemma sm2_representation_strategy21_correctness : sm2_representation_strategy21.
Proof.
  pre_process_default.
  unfold store_u256_limbs.
  Intros x0 x1 x2 x3.
  Exists x0 x1 x2 x3.
  simpl.
  pre_process_default.
Qed.

Lemma sm2_representation_strategy15_correctness : sm2_representation_strategy15.
Proof.
  pre_process_default.
  sep_apply store_u256_materialize_full.
  Intros xs.
  Exists xs.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma sm2_representation_strategy31_correctness : sm2_representation_strategy31.
Proof.
  pre_process_default.
  unfold store_u64_limbs.
  Intros xs.
  Exists xs.
  pre_process_default.
Qed.

Lemma sm2_representation_strategy41_correctness : sm2_representation_strategy41.
Proof.
  pre_process_default.
  unfold store_fp, store_mod.
  entailer!.
Qed.

Lemma sm2_representation_strategy44_correctness : sm2_representation_strategy44.
Proof.
  pre_process_default.
  unfold store_fn, store_mod.
  entailer!.
Qed.

Lemma sm2_representation_strategy12_correctness : sm2_representation_strategy12.
Proof.
  pre_process_default.
Qed.

Lemma sm2_representation_strategy22_correctness : sm2_representation_strategy22.
Proof.
  pre_process_default.
  unfold store_u256_limbs.
  Exists x0 x1 x2 x3.
  simpl.
  pre_process_default.
Qed.

Lemma sm2_representation_strategy32_correctness : sm2_representation_strategy32.
Proof.
  pre_process_default.
  unfold store_u64_limbs.
  Exists xs.
  pre_process_default.
Qed.

Lemma sm2_representation_strategy42_correctness : sm2_representation_strategy42.
Proof.
  pre_process_default.
  unfold store_fp, store_mod.
  entailer!.
Qed.

Lemma sm2_representation_strategy45_correctness : sm2_representation_strategy45.
Proof.
  pre_process_default.
  unfold store_fn, store_mod.
  entailer!.
Qed.
