Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import add_JPoint_boundary_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import SimpleC.EE.Applications_human.sm2.lib.add_JPoint_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma add_JPoint_boundary_strategy20_correctness : add_JPoint_boundary_strategy20.
Proof.
  pre_process_default.
  sep_apply store_fp_materialize_full.
  Intros xs.
  Exists xs.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma add_JPoint_boundary_strategy21_correctness : add_JPoint_boundary_strategy21.
Proof.
  pre_process_default.
  sep_apply store_fp_materialize_full.
  Intros xs.
  Exists xs.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma add_JPoint_boundary_strategy22_correctness : add_JPoint_boundary_strategy22.
Proof.
  pre_process_default.
  sep_apply store_fp_materialize_full.
  Intros xs.
  Exists xs.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.
