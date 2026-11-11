Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ecc_point_overwrite_strategy1_correctness : ecc_point_overwrite_strategy1.
Proof.
  pre_process_default.
  subst q.
  unfold store_mont_jpoint, store_mont_jpoint_coords,
    store_jpoint_fields, store_fp, store_mod, store_u256.
  Intros x y z.
  entailer!.
  repeat sep_apply store_u256_limbs_to_undef_full.
  entailer!.
Qed.
