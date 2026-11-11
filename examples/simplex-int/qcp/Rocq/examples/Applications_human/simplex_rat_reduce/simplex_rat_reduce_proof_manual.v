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
From SimpleC.EE.Applications_human.simplex_rat_reduce Require Import simplex_rat_reduce_goal.
From SimpleC.EE.Applications_human.simplex_rat_reduce Require Import simplex_rat_reduce_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_positive_gcd.simplex_positive_gcd_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Local Open Scope sac.

Lemma proof_of_rat_reduce_safety_wit_3_split_goal_1 : rat_reduce_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_reduce_safety_wit_3_split_goal_2 : rat_reduce_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (simplex_rat_reduce_factor N D ltac:(lia)) as [Hg _].
  rewrite Z.abs_neq in Hg by lia.
  rewrite PreH1. lia.
Qed.

Lemma proof_of_rat_reduce_safety_wit_3 : rat_reduce_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_reduce_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_rat_reduce_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_rat_reduce_safety_wit_4_split_goal_1 : rat_reduce_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_reduce_safety_wit_4_split_goal_2 : rat_reduce_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (simplex_rat_reduce_factor N D ltac:(lia)) as [Hg _].
  rewrite Z.abs_eq in Hg by lia.
  rewrite PreH1. lia.
Qed.

Lemma proof_of_rat_reduce_safety_wit_4 : rat_reduce_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_reduce_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_rat_reduce_safety_wit_4_split_goal_2.
Qed. 

Lemma proof_of_rat_reduce_safety_wit_5_split_goal_1 : rat_reduce_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_reduce_safety_wit_5_split_goal_2 : rat_reduce_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (simplex_rat_reduce_factor N D ltac:(lia)) as [Hg _].
  rewrite Z.abs_neq in Hg by lia.
  rewrite PreH1. lia.
Qed.

Lemma proof_of_rat_reduce_safety_wit_5 : rat_reduce_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_reduce_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_rat_reduce_safety_wit_5_split_goal_2.
Qed. 

Lemma proof_of_rat_reduce_safety_wit_6_split_goal_1 : rat_reduce_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_rat_reduce_safety_wit_6_split_goal_2 : rat_reduce_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  pose proof (simplex_rat_reduce_factor N D ltac:(lia)) as [Hg _].
  rewrite Z.abs_eq in Hg by lia.
  rewrite PreH1. lia.
Qed.

Lemma proof_of_rat_reduce_safety_wit_6 : rat_reduce_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rat_reduce_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_rat_reduce_safety_wit_6_split_goal_2.
Qed. 

Lemma proof_of_rat_reduce_return_wit_1 : rat_reduce_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hret : retval = Z.gcd (Z.abs N) D).
  { rewrite Z.abs_neq by lia. exact PreH1. }
  rewrite Hret.
  set (P := Z.quot N (Z.gcd (Z.abs N) D)).
  set (Q := Z.quot D (Z.gcd (Z.abs N) D)).
  assert (Hr : simplex_rat_reduce_result N D P Q).
  { unfold simplex_rat_reduce_result, P, Q. auto. }
  destruct (simplex_rat_reduce_properties N D P Q INT_MAX
    ltac:(lia) ltac:(lia) Hr) as [HP [HQ [Hcop [Hval [Hzero Hid]]]]].
  destruct (Z.eq_dec (Z.gcd (Z.abs N) D) 1) as [Hg | Hg].
  - destruct (Hid Hg) as [Hpn Hqd]. Right.
    Exists P Q.
    split_pure_spatial.
    + unfold P, Q. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - Left.
    Exists P Q.
    split_pure_spatial.
    + unfold P, Q. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_rat_reduce_return_wit_2 : rat_reduce_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hret : retval = Z.gcd (Z.abs N) D).
  { rewrite Z.abs_eq by lia. exact PreH1. }
  rewrite Hret.
  set (P := Z.quot N (Z.gcd (Z.abs N) D)).
  set (Q := Z.quot D (Z.gcd (Z.abs N) D)).
  assert (Hr : simplex_rat_reduce_result N D P Q).
  { unfold simplex_rat_reduce_result, P, Q. auto. }
  destruct (simplex_rat_reduce_properties N D P Q INT_MAX
    ltac:(lia) ltac:(lia) Hr) as [HP [HQ [Hcop [Hval [Hzero Hid]]]]].
  destruct (Z.eq_dec N 0) as [Hn | Hn];
    destruct (Z.eq_dec (Z.gcd (Z.abs N) D) 1) as [Hg | Hg].
  - destruct (Hzero Hn) as [Hp0 Hq1].
    destruct (Hid Hg) as [Hpn Hqd]. Left. Left. Right.
    Exists P Q.
    split_pure_spatial.
    + unfold P, Q. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - destruct (Hzero Hn) as [Hp0 Hq1]. Left. Left. Left.
    Exists P Q.
    split_pure_spatial.
    + unfold P, Q. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - destruct (Hid Hg) as [Hpn Hqd]. Right.
    Exists P Q.
    split_pure_spatial.
    + unfold P, Q. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - Left. Right.
    Exists P Q.
    split_pure_spatial.
    + unfold P, Q. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
Qed. 

