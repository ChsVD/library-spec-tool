Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_pointer_views_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma byte_pointer_views_strategy1_correctness : byte_pointer_views_strategy1.
Proof.
  pre_process_default.
  subst cursor.
  sep_apply_l_atomic
    (UCharArray.full_split_to_missing_i base index length bytes 0).
  - dump_pre_spatial; lia.
  - replace (base + index * 1) with
      (base + index * sizeof (UCHAR)) by (rewrite sizeof_uchar; lia).
    cancel (UCharArray.missing_i base index 0 length bytes).
    entailer!.
    Intros_r value.
    apply_sepcon_adjoint.
    Intros_p Hvalue.
    subst value.
    cancel.
Qed.

Lemma byte_pointer_views_strategy4_correctness : byte_pointer_views_strategy4.
Proof.
  pre_process_default.
  subst cursor.
  sep_apply_l_atomic
    (UCharArray.full_split_to_missing_i base index length bytes 0).
  - dump_pre_spatial; lia.
  - replace (base + index * 1) with
      (base + index * sizeof (UCHAR)) by (rewrite sizeof_uchar; lia).
    cancel (UCharArray.missing_i base index 0 length bytes).
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    unfold poly_store, poly_undef_store; simpl.
    sep_apply store_uchar_undef_store_uchar.
    cancel.
Qed.

Lemma byte_pointer_views_strategy2_correctness : byte_pointer_views_strategy2.
Proof.
  pre_process_default.
  subst cursor.
  replace (base + index * 1) with
    (base + index * sizeof (UCHAR)) by (rewrite sizeof_uchar; lia).
  sep_apply_l_atomic
    (UCharArray.missing_i_merge_to_full
      base index length (Znth index bytes 0) bytes).
  - dump_pre_spatial; lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
    entailer!.
Qed.

Lemma byte_pointer_views_strategy3_correctness : byte_pointer_views_strategy3.
Proof.
  pre_process_default.
  subst cursor.
  replace (base + index * 1) with
    (base + index * sizeof (UCHAR)) by (rewrite sizeof_uchar; lia).
  sep_apply_l_atomic
    (UCharArray.missing_i_merge_to_full
      base index length value bytes).
  - dump_pre_spatial; lia.
  - cancel.
    entailer!.
Qed.
