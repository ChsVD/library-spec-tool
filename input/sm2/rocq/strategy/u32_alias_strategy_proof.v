Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_goal.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma u32_alias_strategy10_correctness : u32_alias_strategy10.
  unfold u32_alias_strategy10.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  destruct H as [Hab | Hba]; subst.
  - cancel.
    Intros_r y.
    apply_sepcon_adjoint.
    Intros_p Hxy.
    subst y.
    cancel.
  - cancel.
    Intros_r y.
    apply_sepcon_adjoint.
    Intros_p Hxy.
    subst y.
    cancel.
Qed.
