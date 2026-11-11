Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import montg_add_jpoint_cleanup_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.montg_add_jpoint_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma montg_add_jpoint_cleanup_strategy1_correctness : montg_add_jpoint_cleanup_strategy1.
Proof.
  pre_process_default.
  unfold store_fp, store_mod, store_u256, UndefStructPredu32.
  entailer!.
  repeat sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.

Lemma montg_add_jpoint_cleanup_strategy2_correctness : montg_add_jpoint_cleanup_strategy2.
Proof.
  pre_process_default.
  unfold store_fp, store_mod, store_u256, UndefStructPredu32.
  entailer!.
  repeat sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.
