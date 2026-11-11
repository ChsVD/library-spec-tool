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
From SimpleC.EE.Applications_human.simplex_find_entering Require Import simplex_find_entering_goal.
From SimpleC.EE.Applications_human.simplex_find_entering Require Import simplex_find_entering_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib.
Require Import SimpleC.EE.Applications_human.simplex_find_entering.simplex_find_entering_lib.
Local Open Scope sac.

Lemma proof_of_sx_find_entering_entail_wit_1_1_separated_search : sx_find_entering_entail_wit_1_1_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst s_pre row_pre direction_pre entering_pre.
  Left.
  split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
  unfold simplex_enter_skipped. intros; lia.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_1_2_separated_search : sx_find_entering_entail_wit_1_2_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst s_pre row_pre direction_pre entering_pre.
  Right.
  split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
  unfold simplex_enter_skipped. intros; lia.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_2_separated_search : sx_find_entering_entail_wit_2_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_l_atomic (simplex_enter_slots_split S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia)).
 unfold simplex_enter_slot_memory.
 sep_apply_l_atomic (simplex_enter_coeff_split S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search j ltac:(lia) ltac:(lia)).
 assert (EJ : Z.ltb j V_separated_search = true) by (apply Z.ltb_lt; lia).
 rewrite EJ. cbn [andb].
 destruct (Z.eq_dec (Znth j HL_separated_search 0) 0) as [EL|EL];
 destruct (Z.eq_dec (Znth j HU_separated_search 0) 0) as [EU|EU] ;
 [ Left; Right | Right | Left; Left; Left | Left; Left; Right ].
 all: unfold simplex_scan_rat_memory;
   repeat rewrite simplex_scan_rat_member_address;
   rewrite ?EL, ?EU, ?Z.eqb_refl;
   try rewrite (proj2 (Z.eqb_neq _ _) EL);
   try rewrite (proj2 (Z.eqb_neq _ _) EU);
   cbn [negb];
   split_pure_spatial; [sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; first [assumption | lia]].
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_1_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_1_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_1_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_1_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_1_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_1_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_1_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_1_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_1_separated_search : sx_find_entering_entail_wit_3_1_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; auto).
    rewrite EU, EL. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&("increase")) 1).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0))).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [assumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    repeat first [
      progress cbn [negb orb andb]
    | match goal with |- context [Z.eqb ?x ?y] =>
        let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; try lia
      end
    | match goal with |- context [Z.ltb ?x ?y] =>
        let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; try lia
      end ]; try reflexivity; try congruence.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_2_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_2_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_2_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_2_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_2_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_2_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_2_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_2_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_2_separated_search : sx_find_entering_entail_wit_3_2_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; auto).
    rewrite EU, EL. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&("increase")) 1).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0))).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [assumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    repeat first [
      progress cbn [negb orb andb]
    | match goal with |- context [Z.eqb ?x ?y] =>
        let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; try lia
      end
    | match goal with |- context [Z.ltb ?x ?y] =>
        let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; try lia
      end ]; try reflexivity; try congruence.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_3_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_3_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_3_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_3_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_3_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_3_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_3_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_3_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_3_separated_search : sx_find_entering_entail_wit_3_3_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    rewrite EU, EL. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&("increase")) 1).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0))).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [assumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    repeat first [
      progress cbn [negb orb andb]
    | match goal with |- context [Z.eqb ?x ?y] =>
        let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; try lia
      end
    | match goal with |- context [Z.ltb ?x ?y] =>
        let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; try lia
      end ]; try reflexivity; try congruence.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_4_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_4_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_4_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_4_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_4_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_4_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_4_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_4_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_4_separated_search : sx_find_entering_entail_wit_3_4_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; auto).
    rewrite EU, EL. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&("increase")) 1).
    sep_apply_l_atomic (store_int_undef_store_int (&("cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0))).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [assumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    repeat first [
      progress cbn [negb orb andb]
    | match goal with |- context [Z.eqb ?x ?y] =>
        let E := fresh "E" in destruct (Z.eqb x y) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; try lia
      end
    | match goal with |- context [Z.ltb ?x ?y] =>
        let E := fresh "E" in destruct (Z.ltb x y) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; try lia
      end ]; try reflexivity; try congruence.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_5_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_5_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_5_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_5_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_5_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_5_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_5_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_5_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_5_separated_search : sx_find_entering_entail_wit_3_5_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&( "cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&( "increase")) 0).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    eapply simplex_enter_skip_extend; [eassumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    assert (EB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    assert (EC : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EI : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
    { repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) eqn:? end; simpl; try reflexivity; repeat match goal with H : Z.ltb _ _ = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end; lia. }
    rewrite EB, EC. cbn [negb orb]. rewrite EI, EL. cbn [negb].
    assert (EF : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
    assert (EO : Z.ltb 0 (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) = false) by (apply Z.ltb_ge; lia).
    rewrite EF, EO. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_6_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_6_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_6_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_6_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_6_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_6_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_6_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_6_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_6_separated_search : sx_find_entering_entail_wit_3_6_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&( "cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&( "increase")) 0).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    eapply simplex_enter_skip_extend; [eassumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    assert (EB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    assert (EC : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EI : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
    { repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) eqn:? end; simpl; try reflexivity; repeat match goal with H : Z.ltb _ _ = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end; lia. }
    rewrite EB, EC. cbn [negb orb]. rewrite EI, EL. cbn [negb].
    assert (EF : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
    assert (EO : Z.ltb 0 (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) = false) by (apply Z.ltb_ge; lia).
    rewrite EF, EO. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_7_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_7_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_7_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_7_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_7_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_7_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_7_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_7_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_7_separated_search : sx_find_entering_entail_wit_3_7_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&( "cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&( "increase")) 0).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    eapply simplex_enter_skip_extend; [eassumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    assert (EB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    assert (EC : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EI : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
    { repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) eqn:? end; simpl; try reflexivity; repeat match goal with H : Z.ltb _ _ = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end; lia. }
    rewrite EB, EC. cbn [negb orb]. rewrite EI, EL. cbn [negb].
    assert (EF : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
    assert (EO : Z.ltb 0 (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) = false) by (apply Z.ltb_ge; lia).
    rewrite EF, EO. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_8_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_8_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_8_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_8_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_8_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_8_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_8_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_8_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_8_separated_search : sx_find_entering_entail_wit_3_8_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
    sep_apply_l_atomic (store_int_undef_store_int (&( "cmp")) (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0))).
    sep_apply_l_atomic (store_int_undef_store_int (&( "increase")) 0).
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    unfold simplex_enter_skipped in *.
    eapply simplex_enter_skip_extend; [eassumption|].
    unfold simplex_enter_observations, simplex_enter_column.
    assert (EB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
    assert (EC : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
    assert (EI : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
    { repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) eqn:? end; simpl; try reflexivity; repeat match goal with H : Z.ltb _ _ = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end; lia. }
    rewrite EB, EC. cbn [negb orb]. rewrite EI, EL. cbn [negb].
    assert (EF : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
    assert (EO : Z.ltb 0 (simplex_rat_compare_order (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j LN_separated_search 0) (Znth j LD_separated_search 0)) = false) by (apply Z.ltb_ge; lia).
    rewrite EF, EO. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_9_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_9_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_9_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_9_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_9_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_9_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_9_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_9_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_9_separated_search : sx_find_entering_entail_wit_3_9_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pure_spatial.
 - sepcon_assoc_change.
   sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
   unfold simplex_scan_rat_memory.
   repeat rewrite simplex_scan_rat_member_address.
   repeat match goal with
   | H : Znth j ?xs 0 = 0 |- _ => rewrite H
   | H : Znth j ?xs 0 <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   cbn [Z.eqb negb]. sepcon_assoc_change. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_enter_skipped in *.
   eapply simplex_enter_skip_extend; [eassumption|].
   unfold simplex_enter_observations, simplex_enter_column.
   match goal with H : Znth j IB_separated_search 0 <> 0 |- _ =>
    rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_10_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_10_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_10_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_10_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_10_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_10_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_10_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_10_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_10_separated_search : sx_find_entering_entail_wit_3_10_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pure_spatial.
 - sepcon_assoc_change.
   sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
   unfold simplex_scan_rat_memory.
   repeat rewrite simplex_scan_rat_member_address.
   repeat match goal with
   | H : Znth j ?xs 0 = 0 |- _ => rewrite H
   | H : Znth j ?xs 0 <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   cbn [Z.eqb negb]. sepcon_assoc_change. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_enter_skipped in *.
   eapply simplex_enter_skip_extend; [eassumption|].
   unfold simplex_enter_observations, simplex_enter_column.
   match goal with H : Znth j IB_separated_search 0 <> 0 |- _ =>
    rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_11_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_11_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_11_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_11_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_11_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_11_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_11_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_11_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_11_separated_search : sx_find_entering_entail_wit_3_11_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pure_spatial.
 - sepcon_assoc_change.
   sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
   unfold simplex_scan_rat_memory.
   repeat rewrite simplex_scan_rat_member_address.
   repeat match goal with
   | H : Znth j ?xs 0 = 0 |- _ => rewrite H
   | H : Znth j ?xs 0 <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   cbn [Z.eqb negb]. sepcon_assoc_change. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_enter_skipped in *.
   eapply simplex_enter_skip_extend; [eassumption|].
   unfold simplex_enter_observations, simplex_enter_column.
   match goal with H : Znth j IB_separated_search 0 <> 0 |- _ =>
    rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_12_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_12_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_12_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_12_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_12_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_12_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_12_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_12_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_12_separated_search : sx_find_entering_entail_wit_3_12_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 split_pure_spatial.
 - sepcon_assoc_change.
   sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
   unfold simplex_scan_rat_memory.
   repeat rewrite simplex_scan_rat_member_address.
   repeat match goal with
   | H : Znth j ?xs 0 = 0 |- _ => rewrite H
   | H : Znth j ?xs 0 <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   cbn [Z.eqb negb]. sepcon_assoc_change. cancel.
 - split_pures; dump_pre_spatial; try assumption; try lia.
   unfold simplex_enter_skipped in *.
   eapply simplex_enter_skip_extend; [eassumption|].
   unfold simplex_enter_observations, simplex_enter_column.
   match goal with H : Znth j IB_separated_search 0 <> 0 |- _ =>
    rewrite (proj2 (Z.eqb_neq _ _) H)
   end.
   reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_13_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_13_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_13_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_13_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_13_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_13_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_13_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_13_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_13_separated_search : sx_find_entering_entail_wit_3_13_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HS : simplex_enter_skipped IB_separated_search CN_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search D_separated_search (j+1)).
  { unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [exact PreH17|].
    unfold simplex_enter_observations, simplex_enter_column.
    rewrite PreH1, PreH2. reflexivity. }
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; exact PreH18).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; exact PreH19).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_14_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_14_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_14_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_14_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_14_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_14_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_14_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_14_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_14_separated_search : sx_find_entering_entail_wit_3_14_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HS : simplex_enter_skipped IB_separated_search CN_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search D_separated_search (j+1)).
  { unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [exact PreH17|].
    unfold simplex_enter_observations, simplex_enter_column.
    rewrite PreH1, PreH2. reflexivity. }
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; exact PreH18).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; exact PreH19).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_15_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_15_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_15_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_15_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_15_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_15_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_15_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_15_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_15_separated_search : sx_find_entering_entail_wit_3_15_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HS : simplex_enter_skipped IB_separated_search CN_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search D_separated_search (j+1)).
  { unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [exact PreH17|].
    unfold simplex_enter_observations, simplex_enter_column.
    rewrite PreH1, PreH2. reflexivity. }
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; exact PreH18).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; exact PreH19).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_entering_entail_wit_3_16_separated_search_split_goal_1 : sx_find_entering_entail_wit_3_16_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_16_separated_search_split_goal_2 : sx_find_entering_entail_wit_3_16_separated_search_split_goal_2.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_16_separated_search_split_goal_3 : sx_find_entering_entail_wit_3_16_separated_search_split_goal_3.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_16_separated_search_split_goal_spatial : sx_find_entering_entail_wit_3_16_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_entail_wit_3_16_separated_search : sx_find_entering_entail_wit_3_16_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HS : simplex_enter_skipped IB_separated_search CN_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search D_separated_search (j+1)).
  { unfold simplex_enter_skipped in *.
    apply simplex_enter_skip_extend; [exact PreH17|].
    unfold simplex_enter_observations, simplex_enter_column.
    rewrite PreH1, PreH2. reflexivity. }
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (EL : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; exact PreH18).
    assert (EU : Z.eqb (Znth j HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; exact PreH19).
    unfold simplex_scan_rat_memory. rewrite EL, EU. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed. 

Lemma proof_of_sx_find_entering_return_wit_1_separated_search_split_goal_1 : sx_find_entering_return_wit_1_separated_search_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_find_entering_spec, simplex_enter_result.
  left. repeat split; auto. intros; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_1_separated_search : sx_find_entering_return_wit_1_separated_search.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_return_wit_1_separated_search_split_goal_1.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_2_separated_search_split_goal_1 : sx_find_entering_return_wit_2_separated_search_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_find_entering_spec, simplex_enter_result.
  left. repeat split; auto.
  unfold simplex_enter_skipped in *.
  intros i Hi. apply PreH16. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_2_separated_search : sx_find_entering_return_wit_2_separated_search.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_return_wit_2_separated_search_split_goal_1.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_3_separated_search_split_goal_1 : sx_find_entering_return_wit_3_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_3_separated_search_split_goal_spatial : sx_find_entering_return_wit_3_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_3_separated_search : sx_find_entering_return_wit_3_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists j.
 split_pure_spatial.
 - sepcon_assoc_change.
 sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold simplex_scan_rat_memory.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => destruct (Z.eqb a 0) eqn:?; cbn [negb]
  end;
  try (exfalso; repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H end; lia);
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  repeat progress cancel.
 - dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j).
  + lia.
  + unfold simplex_enter_skipped in *; eassumption.
  + left. split; [reflexivity|]. split; [reflexivity|].
    unfold simplex_enter_observations, simplex_enter_column.
    (repeat first [reflexivity |
      match goal with
      | |- context [Z.eqb ?a ?b] =>
        let E := fresh in destruct (Z.eqb a b) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in destruct (Z.ltb a b) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      end]);
    repeat match goal with
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
    end; try reflexivity; exfalso; lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_4_separated_search_split_goal_1 : sx_find_entering_return_wit_4_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_4_separated_search_split_goal_spatial : sx_find_entering_return_wit_4_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_4_separated_search : sx_find_entering_return_wit_4_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists j.
 split_pure_spatial.
 - sepcon_assoc_change.
 sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold simplex_scan_rat_memory.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => destruct (Z.eqb a 0) eqn:?; cbn [negb]
  end;
  try (exfalso; repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H end; lia);
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  repeat progress cancel.
 - dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j).
  + lia.
  + unfold simplex_enter_skipped in *; eassumption.
  + left. split; [reflexivity|]. split; [reflexivity|].
    unfold simplex_enter_observations, simplex_enter_column.
    (repeat first [reflexivity |
      match goal with
      | |- context [Z.eqb ?a ?b] =>
        let E := fresh in destruct (Z.eqb a b) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in destruct (Z.ltb a b) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      end]);
    repeat match goal with
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
    end; try reflexivity; exfalso; lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_5_separated_search_split_goal_1 : sx_find_entering_return_wit_5_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_5_separated_search_split_goal_spatial : sx_find_entering_return_wit_5_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_5_separated_search : sx_find_entering_return_wit_5_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists j.
 split_pure_spatial.
 - sepcon_assoc_change.
 sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold simplex_scan_rat_memory.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => destruct (Z.eqb a 0) eqn:?; cbn [negb]
  end;
  try (exfalso; repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H end; lia);
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  repeat progress cancel.
 - dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j).
  + lia.
  + unfold simplex_enter_skipped in *; eassumption.
  + left. split; [reflexivity|]. split; [reflexivity|].
    unfold simplex_enter_observations, simplex_enter_column.
    (repeat first [reflexivity |
      match goal with
      | |- context [Z.eqb ?a ?b] =>
        let E := fresh in destruct (Z.eqb a b) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in destruct (Z.ltb a b) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      end]);
    repeat match goal with
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
    end; try reflexivity; exfalso; lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_6_separated_search_split_goal_1 : sx_find_entering_return_wit_6_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_6_separated_search_split_goal_spatial : sx_find_entering_return_wit_6_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_6_separated_search : sx_find_entering_return_wit_6_separated_search.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists j.
 split_pure_spatial.
 - sepcon_assoc_change.
 sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold simplex_scan_rat_memory.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => destruct (Z.eqb a 0) eqn:?; cbn [negb]
  end;
  try (exfalso; repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H end; lia);
  rewrite !simplex_scan_rat_member_address.
  sepcon_assoc_change.
  repeat progress cancel.
 - dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j).
  + lia.
  + unfold simplex_enter_skipped in *; eassumption.
  + left. split; [reflexivity|]. split; [reflexivity|].
    unfold simplex_enter_observations, simplex_enter_column.
    (repeat first [reflexivity |
      match goal with
      | |- context [Z.eqb ?a ?b] =>
        let E := fresh in destruct (Z.eqb a b) eqn:E;
        [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in destruct (Z.ltb a b) eqn:E;
        [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
        cbn [negb andb orb]; try solve [exfalso; lia]
      end]);
    repeat match goal with
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
    | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
    | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
    end; try reflexivity; exfalso; lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_7_separated_search_split_goal_1 : sx_find_entering_return_wit_7_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_7_separated_search_split_goal_spatial : sx_find_entering_return_wit_7_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_7_separated_search : sx_find_entering_return_wit_7_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_8_separated_search_split_goal_1 : sx_find_entering_return_wit_8_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_8_separated_search_split_goal_spatial : sx_find_entering_return_wit_8_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_8_separated_search : sx_find_entering_return_wit_8_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_9_separated_search_split_goal_1 : sx_find_entering_return_wit_9_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_9_separated_search_split_goal_spatial : sx_find_entering_return_wit_9_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_9_separated_search : sx_find_entering_return_wit_9_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_10_separated_search_split_goal_1 : sx_find_entering_return_wit_10_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_10_separated_search_split_goal_spatial : sx_find_entering_return_wit_10_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_10_separated_search : sx_find_entering_return_wit_10_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_11_separated_search_split_goal_1 : sx_find_entering_return_wit_11_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_11_separated_search_split_goal_spatial : sx_find_entering_return_wit_11_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_11_separated_search : sx_find_entering_return_wit_11_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (HLzero : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    assert (HUflag : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    rewrite HLzero, HUflag. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    apply (simplex_enter_finish _ V_separated_search j 1 j).
    + lia.
    + exact PreH21.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (HIB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (HCN : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite HIB, HCN. cbn [negb orb].
      assert (Hinc : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
      { apply orb_false_iff. split; apply andb_false_iff; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia]. }
      rewrite Hinc, PreH1. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_12_separated_search_split_goal_1 : sx_find_entering_return_wit_12_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_12_separated_search_split_goal_spatial : sx_find_entering_return_wit_12_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_12_separated_search : sx_find_entering_return_wit_12_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (HLzero : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    assert (HUflag : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    rewrite HLzero, HUflag. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    apply (simplex_enter_finish _ V_separated_search j 1 j).
    + lia.
    + exact PreH21.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (HIB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (HCN : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite HIB, HCN. cbn [negb orb].
      assert (Hinc : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
      { apply orb_false_iff. split; apply andb_false_iff; [right; apply Z.ltb_ge; lia | left; apply Z.ltb_ge; lia]. }
      rewrite Hinc, PreH1. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_13_separated_search_split_goal_1 : sx_find_entering_return_wit_13_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_13_separated_search_split_goal_spatial : sx_find_entering_return_wit_13_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_13_separated_search : sx_find_entering_return_wit_13_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (HLzero : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    assert (HUflag : Z.eqb (Znth j HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    rewrite HLzero, HUflag. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    apply (simplex_enter_finish _ V_separated_search j 1 j).
    + lia.
    + exact PreH21.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (HIB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (HCN : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite HIB, HCN. cbn [negb orb].
      assert (Hinc : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
      { apply orb_false_iff. split; apply andb_false_iff; [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia]. }
      rewrite Hinc, PreH1. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_14_separated_search_split_goal_1 : sx_find_entering_return_wit_14_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_14_separated_search_split_goal_spatial : sx_find_entering_return_wit_14_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_14_separated_search : sx_find_entering_return_wit_14_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (HLzero : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    assert (HUflag : Z.eqb (Znth j HU_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    rewrite HLzero, HUflag. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    apply (simplex_enter_finish _ V_separated_search j 1 j).
    + lia.
    + exact PreH21.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (HIB : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (HCN : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite HIB, HCN. cbn [negb orb].
      assert (Hinc : ((Z.ltb 0 (Znth j CN_separated_search 0) && Z.ltb 0 D_separated_search) || (Z.ltb (Znth j CN_separated_search 0) 0 && Z.ltb D_separated_search 0))%bool = false).
      { apply orb_false_iff. split; apply andb_false_iff; [right; apply Z.ltb_ge; lia | left; apply Z.ltb_ge; lia]. }
      rewrite Hinc, PreH1. reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_15_separated_search_split_goal_1 : sx_find_entering_return_wit_15_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_15_separated_search_split_goal_spatial : sx_find_entering_return_wit_15_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_15_separated_search : sx_find_entering_return_wit_15_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (Hlow : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    assert (Hup : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    rewrite Hlow, Hup. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k := j).
    + lia.
    + unfold simplex_enter_skipped in *. assumption.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (Hb : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (Hc : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hb, Hc. cbn [negb orb].
      assert (Hcp : Z.ltb 0 (Znth j CN_separated_search 0) = true) by (apply Z.ltb_lt; lia).
      assert (Hdp : Z.ltb 0 D_separated_search = true) by (apply Z.ltb_lt; lia).
      assert (Hcn : Z.ltb (Znth j CN_separated_search 0) 0 = false) by (apply Z.ltb_ge; lia).
      assert (Hdn : Z.ltb D_separated_search 0 = false) by (apply Z.ltb_ge; lia).
      rewrite Hcp, Hdp, Hcn, Hdn. cbn [andb orb].
      assert (Hu : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hu.
      assert (Hf : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
      rewrite Hf.
      f_equal. apply Z.ltb_lt. lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_16_separated_search_split_goal_1 : sx_find_entering_return_wit_16_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_16_separated_search_split_goal_spatial : sx_find_entering_return_wit_16_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_16_separated_search : sx_find_entering_return_wit_16_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (Hlow : Z.eqb (Znth j HL_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
    assert (Hup : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    rewrite Hlow, Hup. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k := j).
    + lia.
    + unfold simplex_enter_skipped in *. assumption.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (Hb : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (Hc : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hb, Hc. cbn [negb orb].
      assert (Hcp : Z.ltb 0 (Znth j CN_separated_search 0) = false) by (apply Z.ltb_ge; lia).
      assert (Hdp : Z.ltb 0 D_separated_search = false) by (apply Z.ltb_ge; lia).
      assert (Hcn : Z.ltb (Znth j CN_separated_search 0) 0 = true) by (apply Z.ltb_lt; lia).
      assert (Hdn : Z.ltb D_separated_search 0 = true) by (apply Z.ltb_lt; lia).
      rewrite Hcp, Hdp, Hcn, Hdn. cbn [andb orb].
      assert (Hu : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hu.
      assert (Hf : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
      rewrite Hf.
      f_equal. apply Z.ltb_lt. lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_17_separated_search_split_goal_1 : sx_find_entering_return_wit_17_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_17_separated_search_split_goal_spatial : sx_find_entering_return_wit_17_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_17_separated_search : sx_find_entering_return_wit_17_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (Hlow : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    assert (Hup : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    rewrite Hlow, Hup. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k := j).
    + lia.
    + unfold simplex_enter_skipped in *. assumption.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (Hb : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (Hc : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hb, Hc. cbn [negb orb].
      assert (Hcp : Z.ltb 0 (Znth j CN_separated_search 0) = true) by (apply Z.ltb_lt; lia).
      assert (Hdp : Z.ltb 0 D_separated_search = true) by (apply Z.ltb_lt; lia).
      assert (Hcn : Z.ltb (Znth j CN_separated_search 0) 0 = false) by (apply Z.ltb_ge; lia).
      assert (Hdn : Z.ltb D_separated_search 0 = false) by (apply Z.ltb_ge; lia).
      rewrite Hcp, Hdp, Hcn, Hdn. cbn [andb orb].
      assert (Hu : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hu.
      assert (Hf : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
      rewrite Hf.
      f_equal. apply Z.ltb_lt. lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_18_separated_search_split_goal_1 : sx_find_entering_return_wit_18_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_18_separated_search_split_goal_spatial : sx_find_entering_return_wit_18_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_18_separated_search : sx_find_entering_return_wit_18_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    assert (Hlow : Z.eqb (Znth j HL_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    assert (Hup : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
    rewrite Hlow, Hup. cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k := j).
    + lia.
    + unfold simplex_enter_skipped in *. assumption.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      assert (Hb : Z.eqb (Znth j IB_separated_search 0) 0 = true) by (apply Z.eqb_eq; lia).
      assert (Hc : Z.eqb (Znth j CN_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hb, Hc. cbn [negb orb].
      assert (Hcp : Z.ltb 0 (Znth j CN_separated_search 0) = false) by (apply Z.ltb_ge; lia).
      assert (Hdp : Z.ltb 0 D_separated_search = false) by (apply Z.ltb_ge; lia).
      assert (Hcn : Z.ltb (Znth j CN_separated_search 0) 0 = true) by (apply Z.ltb_lt; lia).
      assert (Hdn : Z.ltb D_separated_search 0 = true) by (apply Z.ltb_lt; lia).
      rewrite Hcp, Hdp, Hcn, Hdn. cbn [andb orb].
      assert (Hu : Z.eqb (Znth j HU_separated_search 0) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hu.
      assert (Hf : Z.eqb (simplex_rat_compare_flag (Znth j VN_separated_search 0) (Znth j VD_separated_search 0) (Znth j UN_separated_search 0) (Znth j UD_separated_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
      rewrite Hf.
      f_equal. apply Z.ltb_lt. lia.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_19_separated_search_split_goal_1 : sx_find_entering_return_wit_19_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_19_separated_search_split_goal_spatial : sx_find_entering_return_wit_19_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_19_separated_search : sx_find_entering_return_wit_19_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_20_separated_search_split_goal_1 : sx_find_entering_return_wit_20_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_20_separated_search_split_goal_spatial : sx_find_entering_return_wit_20_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_20_separated_search : sx_find_entering_return_wit_20_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_21_separated_search_split_goal_1 : sx_find_entering_return_wit_21_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_21_separated_search_split_goal_spatial : sx_find_entering_return_wit_21_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_21_separated_search : sx_find_entering_return_wit_21_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_22_separated_search_split_goal_1 : sx_find_entering_return_wit_22_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_22_separated_search_split_goal_spatial : sx_find_entering_return_wit_22_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_22_separated_search : sx_find_entering_return_wit_22_separated_search.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (-1).
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge S_separated_search R_separated_search V_separated_search CN_separated_search CD_separated_search HL_separated_search HU_separated_search VN_separated_search VD_separated_search LN_separated_search LD_separated_search UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | |- context [Z.eqb ?x ?y] =>
      let H := fresh in
      first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
            |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
    end.
    cbn [negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - split_pures.
    dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + assumption.
    + right. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | |- context [Z.eqb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.eqb x y = true) by (apply Z.eqb_eq; lia)
              |assert (H : Z.eqb x y = false) by (apply Z.eqb_neq; lia)]; rewrite H
      | |- context [Z.ltb ?x ?y] =>
        let H := fresh in
        first [assert (H : Z.ltb x y = true) by (apply Z.ltb_lt; lia)
              |assert (H : Z.ltb x y = false) by (apply Z.ltb_ge; lia)]; rewrite H
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_23_separated_search_split_goal_1 : sx_find_entering_return_wit_23_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_23_separated_search_split_goal_spatial : sx_find_entering_return_wit_23_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_23_separated_search : sx_find_entering_return_wit_23_separated_search.
Proof.
  LLM_pre_process ltac:(auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge
      S_separated_search R_separated_search V_separated_search
      CN_separated_search CD_separated_search HL_separated_search HU_separated_search
      VN_separated_search VD_separated_search LN_separated_search LD_separated_search
      UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
    | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
      let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
    end.
    cbn [Z.eqb negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + unfold simplex_enter_skipped in *; eauto.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
      | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
        let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in first
        [ assert (E : Z.ltb a b = true) by (apply Z.ltb_lt; lia); rewrite E
        | assert (E : Z.ltb a b = false) by (apply Z.ltb_ge; lia); rewrite E ]
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_24_separated_search_split_goal_1 : sx_find_entering_return_wit_24_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_24_separated_search_split_goal_spatial : sx_find_entering_return_wit_24_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_24_separated_search : sx_find_entering_return_wit_24_separated_search.
Proof.
  LLM_pre_process ltac:(auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge
      S_separated_search R_separated_search V_separated_search
      CN_separated_search CD_separated_search HL_separated_search HU_separated_search
      VN_separated_search VD_separated_search LN_separated_search LD_separated_search
      UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
    | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
      let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
    end.
    cbn [Z.eqb negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + unfold simplex_enter_skipped in *; eauto.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
      | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
        let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in first
        [ assert (E : Z.ltb a b = true) by (apply Z.ltb_lt; lia); rewrite E
        | assert (E : Z.ltb a b = false) by (apply Z.ltb_ge; lia); rewrite E ]
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_25_separated_search_split_goal_1 : sx_find_entering_return_wit_25_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_25_separated_search_split_goal_spatial : sx_find_entering_return_wit_25_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_25_separated_search : sx_find_entering_return_wit_25_separated_search.
Proof.
  LLM_pre_process ltac:(auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge
      S_separated_search R_separated_search V_separated_search
      CN_separated_search CD_separated_search HL_separated_search HU_separated_search
      VN_separated_search VD_separated_search LN_separated_search LD_separated_search
      UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
    | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
      let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
    end.
    cbn [Z.eqb negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + unfold simplex_enter_skipped in *; eauto.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
      | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
        let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in first
        [ assert (E : Z.ltb a b = true) by (apply Z.ltb_lt; lia); rewrite E
        | assert (E : Z.ltb a b = false) by (apply Z.ltb_ge; lia); rewrite E ]
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_return_wit_26_separated_search_split_goal_1 : sx_find_entering_return_wit_26_separated_search_split_goal_1.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_26_separated_search_split_goal_spatial : sx_find_entering_return_wit_26_separated_search_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sx_find_entering_return_wit_26_separated_search : sx_find_entering_return_wit_26_separated_search.
Proof.
  LLM_pre_process ltac:(auto).
  Exists j.
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply_r_atomic (simplex_enter_current_slot_merge
      S_separated_search R_separated_search V_separated_search
      CN_separated_search CD_separated_search HL_separated_search HU_separated_search
      VN_separated_search VD_separated_search LN_separated_search LD_separated_search
      UN_separated_search UD_separated_search j ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold simplex_scan_rat_memory.
    repeat match goal with
    | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
    | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
      let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
    end.
    cbn [Z.eqb negb].
    rewrite !simplex_scan_rat_member_address.
    sepcon_assoc_change.
    repeat progress cancel.
  - dump_pre_spatial.
    unfold simplex_find_entering_spec.
    eapply simplex_enter_finish with (k:=j).
    + lia.
    + unfold simplex_enter_skipped in *; eauto.
    + left. split; [reflexivity|]. split; [reflexivity|].
      unfold simplex_enter_observations, simplex_enter_column.
      repeat match goal with
      | H : ?x = 0 |- context [Z.eqb ?x 0] => rewrite H
      | H : ?x <> 0 |- context [Z.eqb ?x 0] =>
        let E := fresh in assert (E : Z.eqb x 0 = false) by (apply Z.eqb_neq; exact H); rewrite E
      | |- context [Z.ltb ?a ?b] =>
        let E := fresh in first
        [ assert (E : Z.ltb a b = true) by (apply Z.ltb_lt; lia); rewrite E
        | assert (E : Z.ltb a b = false) by (apply Z.ltb_ge; lia); rewrite E ]
      end.
      reflexivity.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_13_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_13_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- _ => rewrite Forall_forall in H; apply H
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_13_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_13_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ |- _ =>
      specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_13_separated_search_pure : sx_find_entering_partial_solve_wit_13_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_13_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_13_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_14_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_14_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- _ => rewrite Forall_forall in H; apply H
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_14_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_14_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ |- _ =>
      specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_14_separated_search_pure : sx_find_entering_partial_solve_wit_14_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_14_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_14_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_15_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_15_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- _ => rewrite Forall_forall in H; apply H
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_15_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_15_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ |- _ =>
      specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_15_separated_search_pure : sx_find_entering_partial_solve_wit_15_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_15_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_15_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_16_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_16_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- _ => rewrite Forall_forall in H; apply H
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_16_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_16_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ |- _ =>
      specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_16_separated_search_pure : sx_find_entering_partial_solve_wit_16_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_16_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_16_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_25_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_25_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- 1 <= Znth ?j ?l 0 =>
    apply Forall_forall with (x := Znth j l 0) in H; [exact H |]
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_25_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_25_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i ?l 0)) /\ _) |- 1 <= Znth ?j ?l 0 =>
    specialize (H j); intuition lia
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_25_separated_search_pure : sx_find_entering_partial_solve_wit_25_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_25_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_25_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_26_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_26_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- 1 <= Znth ?j ?l 0 =>
    apply Forall_forall with (x := Znth j l 0) in H; [exact H |]
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_26_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_26_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i ?l 0)) /\ _) |- 1 <= Znth ?j ?l 0 =>
    specialize (H j); intuition lia
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_26_separated_search_pure : sx_find_entering_partial_solve_wit_26_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_26_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_26_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_27_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_27_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- 1 <= Znth ?j ?l 0 =>
    apply Forall_forall with (x := Znth j l 0) in H; [exact H |]
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_27_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_27_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i ?l 0)) /\ _) |- 1 <= Znth ?j ?l 0 =>
    specialize (H j); intuition lia
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_27_separated_search_pure : sx_find_entering_partial_solve_wit_27_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_27_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_27_separated_search_pure_split_goal_2.
Qed. 

Lemma proof_of_sx_find_entering_partial_solve_wit_28_separated_search_pure_split_goal_1 : sx_find_entering_partial_solve_wit_28_separated_search_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) ?l |- 1 <= Znth ?j ?l 0 =>
    apply Forall_forall with (x := Znth j l 0) in H; [exact H |]
  end.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_28_separated_search_pure_split_goal_2 : sx_find_entering_partial_solve_wit_28_separated_search_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i ?l 0)) /\ _) |- 1 <= Znth ?j ?l 0 =>
    specialize (H j); intuition lia
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_28_separated_search_pure : sx_find_entering_partial_solve_wit_28_separated_search_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_28_separated_search_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_28_separated_search_pure_split_goal_2.
Qed. 

