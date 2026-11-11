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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import double_JPoint_goal.
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import double_JPoint_proof_auto.
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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.

Lemma proof_of_double_JPoint_return_wit_1_non_alias_split_goal_1 : double_JPoint_return_wit_1_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst P_non_alias.
  rewrite sm2_point_double_infinity.
  assumption.
Qed.

Lemma proof_of_double_JPoint_return_wit_1_non_alias_split_goal_2 : double_JPoint_return_wit_1_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst P_non_alias.
  rewrite sm2_point_double_infinity.
  assumption.
Qed.

Lemma proof_of_double_JPoint_return_wit_1_non_alias : double_JPoint_return_wit_1_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_double_JPoint_return_wit_1_non_alias_split_goal_1.
  - Goal_apply proof_of_double_JPoint_return_wit_1_non_alias_split_goal_2.
Qed. 

Lemma proof_of_double_JPoint_return_wit_2_in_place : double_JPoint_return_wit_2_in_place.
Proof.
  unfold double_JPoint_return_wit_2_in_place.
  right; intros.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct xs as [|x0 xs].
  { rewrite Zlength_nil in PreH19; discriminate. }
  rewrite Zlength_cons in PreH19.
  destruct xs as [|x1 xs].
  { rewrite Zlength_nil in PreH19; discriminate. }
  rewrite Zlength_cons in PreH19.
  destruct xs as [|x2 xs].
  { rewrite Zlength_nil in PreH19; discriminate. }
  rewrite Zlength_cons in PreH19.
  destruct xs as [|x3 xs].
  { rewrite Zlength_nil in PreH19; discriminate. }
  rewrite Zlength_cons in PreH19.
  destruct xs as [|x4 xs].
  2: { rewrite Zlength_cons in PreH19.
       exfalso; pose proof (Zlength_nonneg xs); lia. }
  rewrite Zlength_nil in PreH19.
  destruct ys as [|y0 ys].
  { rewrite Zlength_nil in PreH14; discriminate. }
  rewrite Zlength_cons in PreH14.
  destruct ys as [|y1 ys].
  { rewrite Zlength_nil in PreH14; discriminate. }
  rewrite Zlength_cons in PreH14.
  destruct ys as [|y2 ys].
  { rewrite Zlength_nil in PreH14; discriminate. }
  rewrite Zlength_cons in PreH14.
  destruct ys as [|y3 ys].
  { rewrite Zlength_nil in PreH14; discriminate. }
  rewrite Zlength_cons in PreH14.
  destruct ys as [|y4 ys].
  2: { rewrite Zlength_cons in PreH14.
       exfalso; pose proof (Zlength_nonneg ys); lia. }
  rewrite Zlength_nil in PreH14.
  destruct zs as [|z0 zs].
  { rewrite Zlength_nil in PreH9; discriminate. }
  rewrite Zlength_cons in PreH9.
  destruct zs as [|z1 zs].
  { rewrite Zlength_nil in PreH9; discriminate. }
  rewrite Zlength_cons in PreH9.
  destruct zs as [|z2 zs].
  { rewrite Zlength_nil in PreH9; discriminate. }
  rewrite Zlength_cons in PreH9.
  destruct zs as [|z3 zs].
  { rewrite Zlength_nil in PreH9; discriminate. }
  rewrite Zlength_cons in PreH9.
  destruct zs as [|z4 zs].
  2: { rewrite Zlength_cons in PreH9.
       exfalso; pose proof (Zlength_nonneg zs); lia. }
  rewrite Zlength_nil in PreH9.
  unfold u64_list_bounded, limb_list_bounded in PreH8, PreH13, PreH18.
  pose proof (PreH18 0 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hx0.
  pose proof (PreH18 1 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hx1.
  pose proof (PreH18 2 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hx2.
  pose proof (PreH13 0 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hy0.
  pose proof (PreH13 1 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hy1.
  pose proof (PreH13 2 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hy2.
  pose proof (PreH8 0 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hz0.
  pose proof (PreH8 1 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hz1.
  pose proof (PreH8 2 ltac:(repeat rewrite Zlength_cons;
    rewrite Zlength_nil; lia)) as Hz2.
  rewrite u64_list_value_four in PreH7, PreH12, PreH17.
  Exists x2 x1 x0 y2 y1 y0 z2 z1 z0.
  subst result_pre.
  repeat first [rewrite Znth0_cons in * | rewrite Znth_cons in * by lia].
  rewrite (u256_missing_high_limb_to_low_cells
    &((pt_pre) # "JPoint" ->ₛ "x" .ₛ "v") x0 x1 x2 x3).
  rewrite (u256_missing_high_limb_to_low_cells
    &((pt_pre) # "JPoint" ->ₛ "y" .ₛ "v") y0 y1 y2 y3).
  rewrite (u256_missing_high_limb_to_low_cells
    &((pt_pre) # "JPoint" ->ₛ "z" .ₛ "v") z0 z1 z2 z3).
  subst P_in_place.
  rewrite sm2_point_double_infinity.
  rewrite PreH17, PreH12, PreH7.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_double_JPoint_return_wit_3_in_place_split_goal_1 : double_JPoint_return_wit_3_in_place_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (jpoint_double_point_of_trace
    JX_in_place JY_in_place JZ_in_place P_in_place).
  assumption.
Qed.

Lemma proof_of_double_JPoint_return_wit_3_in_place_split_goal_2 : double_JPoint_return_wit_3_in_place_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply jdouble_trace_preserves_canonical_infinity;
    eauto using jpoint_double_point_of_trace.
Qed.

Lemma proof_of_double_JPoint_return_wit_3_in_place : double_JPoint_return_wit_3_in_place.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_double_JPoint_return_wit_3_in_place_split_goal_1.
  - Goal_apply proof_of_double_JPoint_return_wit_3_in_place_split_goal_2.
Qed. 

Lemma proof_of_double_JPoint_return_wit_4_non_alias_split_goal_1 : double_JPoint_return_wit_4_non_alias_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (jpoint_double_point_of_trace
    JX_non_alias JY_non_alias JZ_non_alias P_non_alias).
  assumption.
Qed.

Lemma proof_of_double_JPoint_return_wit_4_non_alias_split_goal_2 : double_JPoint_return_wit_4_non_alias_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply jdouble_trace_preserves_canonical_infinity;
    eauto using jpoint_double_point_of_trace.
Qed.

Lemma proof_of_double_JPoint_return_wit_4_non_alias : double_JPoint_return_wit_4_non_alias.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_double_JPoint_return_wit_4_non_alias_split_goal_1.
  - Goal_apply proof_of_double_JPoint_return_wit_4_non_alias_split_goal_2.
Qed. 

Lemma proof_of_double_JPoint_which_implies_wit_1 : double_JPoint_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_double_JPoint_which_implies_wit_2 : double_JPoint_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 
