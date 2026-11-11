From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.simplex_find_entering_preserve Require Import simplex_find_entering_preserve_goal.
From SimpleC.EE.Applications_human.simplex_find_entering_preserve Require Import simplex_find_entering_preserve_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib.
Require Import SimpleC.EE.Applications_human.simplex_find_entering_preserve.simplex_find_entering_preserve_lib.
Local Open Scope sac.

Lemma proof_of_sx_find_entering_entail_wit_1_1 : sx_find_entering_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst s_pre row_pre direction_pre entering_pre.
  Left.
  split_pure_spatial.
  - repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia | unfold simplex_enter_skipped; intros; lia].
Qed.

Lemma proof_of_sx_find_entering_entail_wit_1_2 : sx_find_entering_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst s_pre row_pre direction_pre entering_pre.
  Right.
  split_pure_spatial.
  - repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia | unfold simplex_enter_skipped; intros; lia].
Qed.

Lemma proof_of_sx_find_entering_entail_wit_2 : sx_find_entering_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
  { apply existsb_exists. exists j. split; [apply In_Zrange; lia | apply Z.eqb_refl]. }
  sep_apply (IntArray.full_split_to_missing_i &(S_framed_search # "SxState" ->ₛ "is_basic") j V_framed_search IB_framed_search 0 ltac:(lia)).
  sep_apply (read_slot_focus__read_focus S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  sep_apply (num_focus__entry_focus S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_scan_read_slot. rewrite HA. simpl.
  destruct (Z.eqb_spec (Znth j HL_framed_search 0) 0) as [HL|HL];
  destruct (Z.eqb_spec (Znth j HU_framed_search 0) 0) as [HU|HU]; simpl;
    [Left; Left; Left; Left | Right | Left; Left; Left; Right | Left; Left; Right].
  all: split_pure_spatial.
  all: try (split_pures; dump_pre_spatial; first [assumption | reflexivity | lia | tauto]).
  all: unfold simplex_scan_rat_memory, simplex_enter_num_cell; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel.
all: rewrite (Z.mul_comm (sizeof("SxRat")) 24); simpl; csimpl; cancel.
Show.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_1_split_goal_1 : sx_find_entering_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => let H := fresh in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try (exfalso; lia); simpl
  | |- context [Z.ltb ?a ?b] => let H := fresh in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try (exfalso; lia); simpl
  end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_1_split_goal_2 : sx_find_entering_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_1_split_goal_3 : sx_find_entering_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_1_split_goal_spatial : sx_find_entering_entail_wit_3_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
  cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_skip by lia.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => let H := fresh in destruct (Z.eqb a 0) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try contradiction; simpl
  end;
  unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel; try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_1 : sx_find_entering_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_1_split_goal_spatial.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_1_split_goal_1.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_1_split_goal_2.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_1_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_2_split_goal_1 : sx_find_entering_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => let H := fresh in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try (exfalso; lia); simpl
  | |- context [Z.ltb ?a ?b] => let H := fresh in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try (exfalso; lia); simpl
  end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_2_split_goal_2 : sx_find_entering_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_2_split_goal_3 : sx_find_entering_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_2_split_goal_spatial : sx_find_entering_entail_wit_3_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
  cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_skip by lia.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => let H := fresh in destruct (Z.eqb a 0) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try contradiction; simpl
  end;
  unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel; try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_2 : sx_find_entering_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_2_split_goal_spatial.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_2_split_goal_1.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_2_split_goal_2.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_2_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_3_split_goal_1 : sx_find_entering_entail_wit_3_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => let H := fresh in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try (exfalso; lia); simpl
  | |- context [Z.ltb ?a ?b] => let H := fresh in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try (exfalso; lia); simpl
  end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_3_split_goal_2 : sx_find_entering_entail_wit_3_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_3_split_goal_3 : sx_find_entering_entail_wit_3_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_3_split_goal_spatial : sx_find_entering_entail_wit_3_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
  cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_skip by lia.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => let H := fresh in destruct (Z.eqb a 0) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try contradiction; simpl
  end;
  unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel; try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_3 : sx_find_entering_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_3_split_goal_spatial.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_3_split_goal_1.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_3_split_goal_2.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_3_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_4_split_goal_1 : sx_find_entering_entail_wit_3_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => let H := fresh in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try (exfalso; lia); simpl
  | |- context [Z.ltb ?a ?b] => let H := fresh in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try (exfalso; lia); simpl
  end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_4_split_goal_2 : sx_find_entering_entail_wit_3_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_4_split_goal_3 : sx_find_entering_entail_wit_3_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_4_split_goal_spatial : sx_find_entering_entail_wit_3_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
  cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_skip by lia.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => let H := fresh in destruct (Z.eqb a 0) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try contradiction; simpl
  end;
  unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel; try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_4 : sx_find_entering_entail_wit_3_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_4_split_goal_spatial.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_4_split_goal_1.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_4_split_goal_2.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_4_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_5_split_goal_1 : sx_find_entering_entail_wit_3_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => let H := fresh in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try (exfalso; lia); simpl
  | |- context [Z.ltb ?a ?b] => let H := fresh in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try (exfalso; lia); simpl
  end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_5_split_goal_2 : sx_find_entering_entail_wit_3_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_5_split_goal_3 : sx_find_entering_entail_wit_3_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_5_split_goal_spatial : sx_find_entering_entail_wit_3_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
  cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_skip by lia.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => let H := fresh in destruct (Z.eqb a 0) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try contradiction; simpl
  end;
  unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel; try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_5 : sx_find_entering_entail_wit_3_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_5_split_goal_spatial.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_5_split_goal_1.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_5_split_goal_2.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_5_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_6_split_goal_1 : sx_find_entering_entail_wit_3_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => let H := fresh in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try (exfalso; lia); simpl
  | |- context [Z.ltb ?a ?b] => let H := fresh in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try (exfalso; lia); simpl
  end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_6_split_goal_2 : sx_find_entering_entail_wit_3_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_6_split_goal_3 : sx_find_entering_entail_wit_3_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_6_split_goal_spatial : sx_find_entering_entail_wit_3_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
  cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_skip by lia.
  repeat match goal with
  | |- context [Z.eqb ?a 0] => let H := fresh in destruct (Z.eqb a 0) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try contradiction; simpl
  end;
  unfold simplex_scan_rat_memory; csimpl; sepcon_right_assoc;
    repeat match goal with |- _ |-- ?p ** _ => cancel p end; cancel; try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_6 : sx_find_entering_entail_wit_3_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_6_split_goal_spatial.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_6_split_goal_1.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_6_split_goal_2.
  Goal_apply proof_of_sx_find_entering_entail_wit_3_6_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_7_split_goal_1 : sx_find_entering_entail_wit_3_7_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 match goal with H : ?r = simplex_rat_compare_flag ?a ?b ?c ?d,
                 H1 : ?r = 1 |- _ => rewrite <- H, H1 end.
 repeat first [progress cbn [negb orb andb] |
   match goal with
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); try lia
   end]; try lia; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_7_split_goal_2 : sx_find_entering_entail_wit_3_7_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_7_split_goal_3 : sx_find_entering_entail_wit_3_7_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_7_split_goal_spatial : sx_find_entering_entail_wit_3_7_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 sep_apply_r_atomic (num_restore__lower_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search)=true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0); try lia
 end; cbn [negb orb andb].
 unfold simplex_scan_rat_memory.
 csimpl.
 do 8 (try match goal with |- _ |-- ?P ** _ => cancel P end).
 cancel.

Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_7 : sx_find_entering_entail_wit_3_7.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_7_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_7_split_goal_1.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_7_split_goal_2.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_7_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_8_split_goal_1 : sx_find_entering_entail_wit_3_8_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 match goal with H : ?r = simplex_rat_compare_flag ?a ?b ?c ?d,
                 H1 : ?r = 1 |- _ => rewrite <- H, H1 end.
 repeat first [progress cbn [negb orb andb] |
   match goal with
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); try lia
   end]; try lia; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_8_split_goal_2 : sx_find_entering_entail_wit_3_8_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_8_split_goal_3 : sx_find_entering_entail_wit_3_8_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_8_split_goal_spatial : sx_find_entering_entail_wit_3_8_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 sep_apply_r_atomic (num_restore__lower_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search)=true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0); try lia
 end; cbn [negb orb andb].
 unfold simplex_scan_rat_memory.
 csimpl.
 do 8 (try match goal with |- _ |-- ?P ** _ => cancel P end).
 cancel.

Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_8 : sx_find_entering_entail_wit_3_8.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_8_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_8_split_goal_1.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_8_split_goal_2.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_8_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_9_split_goal_1 : sx_find_entering_entail_wit_3_9_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 match goal with H : ?r = simplex_rat_compare_flag ?a ?b ?c ?d,
                 H1 : ?r = 1 |- _ => rewrite <- H, H1 end.
 repeat first [progress cbn [negb orb andb] |
   match goal with
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); try lia
   end]; try lia; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_9_split_goal_2 : sx_find_entering_entail_wit_3_9_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_9_split_goal_3 : sx_find_entering_entail_wit_3_9_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_9_split_goal_spatial : sx_find_entering_entail_wit_3_9_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 sep_apply_r_atomic (num_restore__lower_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search)=true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0); try lia
 end; cbn [negb orb andb].
 unfold simplex_scan_rat_memory.
 csimpl.
 do 8 (try match goal with |- _ |-- ?P ** _ => cancel P end).
 cancel.

Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_9 : sx_find_entering_entail_wit_3_9.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_9_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_9_split_goal_1.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_9_split_goal_2.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_9_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_10_split_goal_1 : sx_find_entering_entail_wit_3_10_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 match goal with H : ?r = simplex_rat_compare_flag ?a ?b ?c ?d,
                 H1 : ?r = 1 |- _ => rewrite <- H, H1 end.
 repeat first [progress cbn [negb orb andb] |
   match goal with
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); try lia
   end]; try lia; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_10_split_goal_2 : sx_find_entering_entail_wit_3_10_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_10_split_goal_3 : sx_find_entering_entail_wit_3_10_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_10_split_goal_spatial : sx_find_entering_entail_wit_3_10_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 sep_apply_r_atomic (num_restore__lower_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search)=true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0); try lia
 end; cbn [negb orb andb].
 unfold simplex_scan_rat_memory.
 csimpl.
 do 8 (try match goal with |- _ |-- ?P ** _ => cancel P end).
 cancel.

Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_10 : sx_find_entering_entail_wit_3_10.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_10_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_10_split_goal_1.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_10_split_goal_2.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_10_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_11_split_goal_1 : sx_find_entering_entail_wit_3_11_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 match goal with H : ?r = simplex_rat_compare_flag ?a ?b ?c ?d,
                 H1 : ?r = 1 |- _ => rewrite <- H, H1 end.
 repeat first [progress cbn [negb orb andb] |
   match goal with
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); try lia
   end]; try lia; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_11_split_goal_2 : sx_find_entering_entail_wit_3_11_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_11_split_goal_3 : sx_find_entering_entail_wit_3_11_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_11_split_goal_spatial : sx_find_entering_entail_wit_3_11_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 sep_apply_r_atomic (num_restore__lower_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search)=true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0); try lia
 end; cbn [negb orb andb].
 unfold simplex_scan_rat_memory.
 csimpl.
 do 8 (try match goal with |- _ |-- ?P ** _ => cancel P end).
 cancel.

Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_11 : sx_find_entering_entail_wit_3_11.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_11_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_11_split_goal_1.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_11_split_goal_2.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_11_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_12_split_goal_1 : sx_find_entering_entail_wit_3_12_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial. unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 match goal with H : ?r = simplex_rat_compare_flag ?a ?b ?c ?d,
                 H1 : ?r = 1 |- _ => rewrite <- H, H1 end.
 repeat first [progress cbn [negb orb andb] |
   match goal with
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); try lia
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y); try lia
   end]; try lia; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_12_split_goal_2 : sx_find_entering_entail_wit_3_12_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_12_split_goal_3 : sx_find_entering_entail_wit_3_12_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_12_split_goal_spatial : sx_find_entering_entail_wit_3_12_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 sep_apply_r_atomic (num_restore__lower_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search)=true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 repeat match goal with
 | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0); try lia
 end; cbn [negb orb andb].
 unfold simplex_scan_rat_memory.
 csimpl.
 do 8 (try match goal with |- _ |-- ?P ** _ => cancel P end).
 cancel.

Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_12 : sx_find_entering_entail_wit_3_12.
Proof.
aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_12_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_12_split_goal_1.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_12_split_goal_2.
 - Goal_apply proof_of_sx_find_entering_entail_wit_3_12_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_13_split_goal_1 : sx_find_entering_entail_wit_3_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  assert (Z.eqb (Znth j IB_framed_search 0) 0 = false) as HB by (apply Z.eqb_neq; assumption).
  rewrite HB. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_13_split_goal_2 : sx_find_entering_entail_wit_3_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_13_split_goal_3 : sx_find_entering_entail_wit_3_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_13_split_goal_spatial : sx_find_entering_entail_wit_3_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__basic_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
  cancel.
  pose proof (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)) as HM.
  rewrite replace_Znth_Znth in HM.
  sep_apply_r_atomic HM.
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel.
  unfold simplex_scan_read_slot.
  rewrite active__basic_skip by lia.
  repeat match goal with H : Znth j ?l 0 = 0 |- _ => rewrite H end.
  repeat match goal with H : Znth j ?l 0 <> 0 |- _ => let HB := fresh in assert (Z.eqb (Znth j l 0) 0 = false) as HB by (apply Z.eqb_neq; exact H); rewrite HB; clear HB end.
  cbn [Z.eqb andb orb negb].
  unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  cancel (IntArray.missing_i (&(S_framed_search # "SxState" ->ₛ "is_basic")) j 0 V_framed_search IB_framed_search).
  cancel ((&(S_framed_search # "SxState" ->ₛ "is_basic") + j * sizeof(INT)) # Int |-> Znth j IB_framed_search 0).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  repeat cancel emp.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_13 : sx_find_entering_entail_wit_3_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_13_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_13_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_13_split_goal_2.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_13_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_14_split_goal_1 : sx_find_entering_entail_wit_3_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  assert (Z.eqb (Znth j IB_framed_search 0) 0 = false) as HB by (apply Z.eqb_neq; assumption).
  rewrite HB. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_14_split_goal_2 : sx_find_entering_entail_wit_3_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_14_split_goal_3 : sx_find_entering_entail_wit_3_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_14_split_goal_spatial : sx_find_entering_entail_wit_3_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__basic_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
  cancel.
  pose proof (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)) as HM.
  rewrite replace_Znth_Znth in HM.
  sep_apply_r_atomic HM.
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel.
  unfold simplex_scan_read_slot.
  rewrite active__basic_skip by lia.
  repeat match goal with H : Znth j ?l 0 = 0 |- _ => rewrite H end.
  repeat match goal with H : Znth j ?l 0 <> 0 |- _ => let HB := fresh in assert (Z.eqb (Znth j l 0) 0 = false) as HB by (apply Z.eqb_neq; exact H); rewrite HB; clear HB end.
  cbn [Z.eqb andb orb negb].
  unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  cancel (IntArray.missing_i (&(S_framed_search # "SxState" ->ₛ "is_basic")) j 0 V_framed_search IB_framed_search).
  cancel ((&(S_framed_search # "SxState" ->ₛ "is_basic") + j * sizeof(INT)) # Int |-> Znth j IB_framed_search 0).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  repeat cancel emp.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_14 : sx_find_entering_entail_wit_3_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_14_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_14_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_14_split_goal_2.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_14_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_15_split_goal_1 : sx_find_entering_entail_wit_3_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  assert (Z.eqb (Znth j IB_framed_search 0) 0 = false) as HB by (apply Z.eqb_neq; assumption).
  rewrite HB. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_15_split_goal_2 : sx_find_entering_entail_wit_3_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_15_split_goal_3 : sx_find_entering_entail_wit_3_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_15_split_goal_spatial : sx_find_entering_entail_wit_3_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__basic_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
  cancel.
  pose proof (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)) as HM.
  rewrite replace_Znth_Znth in HM.
  sep_apply_r_atomic HM.
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel.
  unfold simplex_scan_read_slot.
  rewrite active__basic_skip by lia.
  repeat match goal with H : Znth j ?l 0 = 0 |- _ => rewrite H end.
  repeat match goal with H : Znth j ?l 0 <> 0 |- _ => let HB := fresh in assert (Z.eqb (Znth j l 0) 0 = false) as HB by (apply Z.eqb_neq; exact H); rewrite HB; clear HB end.
  cbn [Z.eqb andb orb negb].
  unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  cancel (IntArray.missing_i (&(S_framed_search # "SxState" ->ₛ "is_basic")) j 0 V_framed_search IB_framed_search).
  cancel ((&(S_framed_search # "SxState" ->ₛ "is_basic") + j * sizeof(INT)) # Int |-> Znth j IB_framed_search 0).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_15 : sx_find_entering_entail_wit_3_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_15_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_15_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_15_split_goal_2.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_15_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_16_split_goal_1 : sx_find_entering_entail_wit_3_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  assert (Z.eqb (Znth j IB_framed_search 0) 0 = false) as HB by (apply Z.eqb_neq; assumption).
  rewrite HB. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_16_split_goal_2 : sx_find_entering_entail_wit_3_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_16_split_goal_3 : sx_find_entering_entail_wit_3_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_16_split_goal_spatial : sx_find_entering_entail_wit_3_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__basic_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
  cancel.
  pose proof (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)) as HM.
  rewrite replace_Znth_Znth in HM.
  sep_apply_r_atomic HM.
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel.
  unfold simplex_scan_read_slot.
  rewrite active__basic_skip by lia.
  repeat match goal with H : Znth j ?l 0 = 0 |- _ => rewrite H end.
  repeat match goal with H : Znth j ?l 0 <> 0 |- _ => let HB := fresh in assert (Z.eqb (Znth j l 0) 0 = false) as HB by (apply Z.eqb_neq; exact H); rewrite HB; clear HB end.
  cbn [Z.eqb andb orb negb].
  unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  cancel (IntArray.missing_i (&(S_framed_search # "SxState" ->ₛ "is_basic")) j 0 V_framed_search IB_framed_search).
  cancel ((&(S_framed_search # "SxState" ->ₛ "is_basic") + j * sizeof(INT)) # Int |-> Znth j IB_framed_search 0).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_16 : sx_find_entering_entail_wit_3_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_16_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_16_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_16_split_goal_2.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_16_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_17_split_goal_1 : sx_find_entering_entail_wit_3_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_enter_skipped in *.
  apply simplex_enter_skip_extend; [assumption|].
  unfold simplex_enter_observations, simplex_enter_column.
  assert (Z.eqb (Znth j IB_framed_search 0) 0 = false) as HB by (apply Z.eqb_neq; assumption).
  rewrite HB. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_17_split_goal_2 : sx_find_entering_entail_wit_3_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_17_split_goal_3 : sx_find_entering_entail_wit_3_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_17_split_goal_spatial : sx_find_entering_entail_wit_3_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__basic_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
  cancel.
  pose proof (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)) as HM.
  rewrite replace_Znth_Znth in HM.
  sep_apply_r_atomic HM.
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel.
  unfold simplex_scan_read_slot.
  rewrite active__basic_skip by lia.
  repeat match goal with H : Znth j ?l 0 = 0 |- _ => rewrite H end.
  repeat match goal with H : Znth j ?l 0 <> 0 |- _ => let HB := fresh in assert (Z.eqb (Znth j l 0) 0 = false) as HB by (apply Z.eqb_neq; exact H); rewrite HB; clear HB end.
  cbn [Z.eqb andb orb negb].
  unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- ?P ** _ => cancel P end.
  match goal with |- _ |-- emp ** (?P ** _) => cancel P end.
  match goal with |- _ |-- emp ** (?P ** _) => cancel P end.
  cancel (IntArray.missing_i (&(S_framed_search # "SxState" ->ₛ "is_basic")) j 0 V_framed_search IB_framed_search).
  cancel ((&(S_framed_search # "SxState" ->ₛ "is_basic") + j * sizeof(INT)) # Int |-> Znth j IB_framed_search 0).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  repeat cancel emp.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_17 : sx_find_entering_entail_wit_3_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_17_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_17_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_17_split_goal_2.
  - Goal_apply proof_of_sx_find_entering_entail_wit_3_17_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_18_split_goal_1 : sx_find_entering_entail_wit_3_18_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 assert (HC : Znth j CN_framed_search 0 = 0) by assumption.
 rewrite HC, Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_18_split_goal_2 : sx_find_entering_entail_wit_3_18_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_18_split_goal_3 : sx_find_entering_entail_wit_3_18_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_18_split_goal_spatial : sx_find_entering_entail_wit_3_18_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__zero_coeff_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel.
 sep_apply_r_atomic (basic_restore__zero_coeff_skip (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search IB_framed_search ltac:(lia)).
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite range_active__zero_coeff_skip by lia.
 assert (EHL : Z.eqb (Znth j HL_framed_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
 rewrite EHL.
 assert (EHU : Z.eqb (Znth j HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
 rewrite EHU.
 cbn [negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 all: repeat (progress (cancel emp)).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_18 : sx_find_entering_entail_wit_3_18.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_18_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_18_split_goal_1.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_18_split_goal_2.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_18_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_19_split_goal_1 : sx_find_entering_entail_wit_3_19_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 assert (HC : Znth j CN_framed_search 0 = 0) by assumption.
 rewrite HC, Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_19_split_goal_2 : sx_find_entering_entail_wit_3_19_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_19_split_goal_3 : sx_find_entering_entail_wit_3_19_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_19_split_goal_spatial : sx_find_entering_entail_wit_3_19_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__zero_coeff_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel.
 sep_apply_r_atomic (basic_restore__zero_coeff_skip (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search IB_framed_search ltac:(lia)).
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite range_active__zero_coeff_skip by lia.
 assert (EHL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EHL.
 assert (EHU : Z.eqb (Znth j HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
 rewrite EHU.
 cbn [negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 all: repeat (progress (cancel emp)).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_19 : sx_find_entering_entail_wit_3_19.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_19_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_19_split_goal_1.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_19_split_goal_2.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_19_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_20_split_goal_1 : sx_find_entering_entail_wit_3_20_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 assert (HC : Znth j CN_framed_search 0 = 0) by assumption.
 rewrite HC, Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_20_split_goal_2 : sx_find_entering_entail_wit_3_20_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_20_split_goal_3 : sx_find_entering_entail_wit_3_20_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_20_split_goal_spatial : sx_find_entering_entail_wit_3_20_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__zero_coeff_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel.
 sep_apply_r_atomic (basic_restore__zero_coeff_skip (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search IB_framed_search ltac:(lia)).
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite range_active__zero_coeff_skip by lia.
 assert (EHL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EHL.
 assert (EHU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EHU.
 cbn [negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 all: repeat (progress (cancel emp)).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_20 : sx_find_entering_entail_wit_3_20.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_20_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_20_split_goal_1.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_20_split_goal_2.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_20_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_21_split_goal_1 : sx_find_entering_entail_wit_3_21_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 assert (HC : Znth j CN_framed_search 0 = 0) by assumption.
 rewrite HC, Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_21_split_goal_2 : sx_find_entering_entail_wit_3_21_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_21_split_goal_3 : sx_find_entering_entail_wit_3_21_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_21_split_goal_spatial : sx_find_entering_entail_wit_3_21_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__zero_coeff_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel.
 sep_apply_r_atomic (basic_restore__zero_coeff_skip (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search IB_framed_search ltac:(lia)).
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite range_active__zero_coeff_skip by lia.
 assert (EHL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EHL.
 assert (EHU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EHU.
 cbn [negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 all: repeat (progress (cancel emp)).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_21 : sx_find_entering_entail_wit_3_21.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_21_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_21_split_goal_1.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_21_split_goal_2.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_21_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_22_split_goal_1 : sx_find_entering_entail_wit_3_22_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_enter_skipped in *.
 eapply simplex_enter_skip_extend; [eassumption|].
 unfold simplex_enter_observations, simplex_enter_column.
 assert (HC : Znth j CN_framed_search 0 = 0) by assumption.
 rewrite HC, Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_22_split_goal_2 : sx_find_entering_entail_wit_3_22_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_22_split_goal_3 : sx_find_entering_entail_wit_3_22_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_22_split_goal_spatial : sx_find_entering_entail_wit_3_22_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__zero_coeff_skip S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel.
 sep_apply_r_atomic (basic_restore__zero_coeff_skip (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search IB_framed_search ltac:(lia)).
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite range_active__zero_coeff_skip by lia.
 assert (EHL : Z.eqb (Znth j HL_framed_search 0) 0 = true) by (apply Z.eqb_eq; assumption).
 rewrite EHL.
 assert (EHU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; assumption).
 rewrite EHU.
 cbn [negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 all: repeat (progress (cancel emp)).
Qed.

Lemma proof_of_sx_find_entering_entail_wit_3_22 : sx_find_entering_entail_wit_3_22.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_22_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_22_split_goal_1.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_22_split_goal_2.
 Goal_apply proof_of_sx_find_entering_entail_wit_3_22_split_goal_3.
Qed.

Lemma proof_of_sx_find_entering_return_wit_1_split_goal_1 : sx_find_entering_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_find_entering_spec, simplex_enter_result.
  left. repeat split; auto. intros k Hk.
  match goal with H : simplex_enter_skipped _ _ _ _ _ _ _ _ _ _ _ j |- _ => apply H; lia end.
Qed.

Lemma proof_of_sx_find_entering_return_wit_1 : sx_find_entering_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_2_split_goal_1 : sx_find_entering_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold simplex_find_entering_spec, simplex_enter_result.
  left. repeat split; auto. intros k Hk.
  match goal with H : simplex_enter_skipped _ _ _ _ _ _ _ _ _ _ _ j |- _ => apply H; lia end.
Qed.

Lemma proof_of_sx_find_entering_return_wit_2 : sx_find_entering_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sx_find_entering_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_3_split_goal_1 : sx_find_entering_return_wit_3_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 rewrite PreH28.
 assert (EC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (CP : Z.ltb 0 (Znth j CN_framed_search 0) = true) by (apply Z.ltb_lt; lia).
 assert (CN : Z.ltb (Znth j CN_framed_search 0) 0 = false) by (apply Z.ltb_ge; lia).
 assert (DP : Z.ltb 0 D_framed_search = false) by (apply Z.ltb_ge; lia).
 rewrite EC, CP, CN, DP. cbn.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HF : Z.eqb (simplex_rat_compare_flag (Znth j VN_framed_search 0) (Znth j VD_framed_search 0) (Znth j LN_framed_search 0) (Znth j LD_framed_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
 rewrite HF. f_equal. apply Z.ltb_lt. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_3_split_goal_spatial : sx_find_entering_return_wit_3_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HU. cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
Qed.

Lemma proof_of_sx_find_entering_return_wit_3 : sx_find_entering_return_wit_3.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_3_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_4_split_goal_1 : sx_find_entering_return_wit_4_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 rewrite PreH28.
 assert (EC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (CP : Z.ltb 0 (Znth j CN_framed_search 0) = false) by (apply Z.ltb_ge; lia).
 assert (CN : Z.ltb (Znth j CN_framed_search 0) 0 = true) by (apply Z.ltb_lt; lia).
 assert (DP : Z.ltb D_framed_search 0 = false) by (apply Z.ltb_ge; lia).
 rewrite EC, CP, CN, DP. cbn.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HF : Z.eqb (simplex_rat_compare_flag (Znth j VN_framed_search 0) (Znth j VD_framed_search 0) (Znth j LN_framed_search 0) (Znth j LD_framed_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
 rewrite HF. f_equal. apply Z.ltb_lt. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_4_split_goal_spatial : sx_find_entering_return_wit_4_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HU. cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
Qed.

Lemma proof_of_sx_find_entering_return_wit_4 : sx_find_entering_return_wit_4.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_4_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_5_split_goal_1 : sx_find_entering_return_wit_5_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 rewrite PreH28.
 assert (EC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (CP : Z.ltb 0 (Znth j CN_framed_search 0) = true) by (apply Z.ltb_lt; lia).
 assert (CN : Z.ltb (Znth j CN_framed_search 0) 0 = false) by (apply Z.ltb_ge; lia).
 assert (DP : Z.ltb 0 D_framed_search = false) by (apply Z.ltb_ge; lia).
 rewrite EC, CP, CN, DP. cbn.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HF : Z.eqb (simplex_rat_compare_flag (Znth j VN_framed_search 0) (Znth j VD_framed_search 0) (Znth j LN_framed_search 0) (Znth j LD_framed_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
 rewrite HF. f_equal. apply Z.ltb_lt. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_5_split_goal_spatial : sx_find_entering_return_wit_5_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HU. cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
Qed.

Lemma proof_of_sx_find_entering_return_wit_5 : sx_find_entering_return_wit_5.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_5_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_6_split_goal_1 : sx_find_entering_return_wit_6_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 rewrite PreH28.
 assert (EC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (CP : Z.ltb 0 (Znth j CN_framed_search 0) = false) by (apply Z.ltb_ge; lia).
 assert (CN : Z.ltb (Znth j CN_framed_search 0) 0 = true) by (apply Z.ltb_lt; lia).
 assert (DP : Z.ltb D_framed_search 0 = false) by (apply Z.ltb_ge; lia).
 rewrite EC, CP, CN, DP. cbn.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HF : Z.eqb (simplex_rat_compare_flag (Znth j VN_framed_search 0) (Znth j VD_framed_search 0) (Znth j LN_framed_search 0) (Znth j LD_framed_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
 rewrite HF. f_equal. apply Z.ltb_lt. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_6_split_goal_spatial : sx_find_entering_return_wit_6_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HU : Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HU. cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
Qed.

Lemma proof_of_sx_find_entering_return_wit_6 : sx_find_entering_return_wit_6.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_6_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_7_split_goal_1 : sx_find_entering_return_wit_7_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 rewrite PreH24.
 assert (EC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (CP : Z.ltb 0 (Znth j CN_framed_search 0) = true) by (apply Z.ltb_lt; lia).
 assert (CN : Z.ltb (Znth j CN_framed_search 0) 0 = false) by (apply Z.ltb_ge; lia).
 assert (DP : Z.ltb 0 D_framed_search = false) by (apply Z.ltb_ge; lia).
 rewrite EC, CP, CN, DP. cbn.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HF : Z.eqb (simplex_rat_compare_flag (Znth j VN_framed_search 0) (Znth j VD_framed_search 0) (Znth j LN_framed_search 0) (Znth j LD_framed_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
 rewrite HF. f_equal. apply Z.ltb_lt. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_7_split_goal_spatial : sx_find_entering_return_wit_7_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HU : Z.eqb (Znth j HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 rewrite HU. cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_7 : sx_find_entering_return_wit_7.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_7_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_8_split_goal_1 : sx_find_entering_return_wit_8_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 rewrite PreH24.
 assert (EC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 assert (CP : Z.ltb 0 (Znth j CN_framed_search 0) = false) by (apply Z.ltb_ge; lia).
 assert (CN : Z.ltb (Znth j CN_framed_search 0) 0 = true) by (apply Z.ltb_lt; lia).
 assert (DP : Z.ltb D_framed_search 0 = false) by (apply Z.ltb_ge; lia).
 rewrite EC, CP, CN, DP. cbn.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HF : Z.eqb (simplex_rat_compare_flag (Znth j VN_framed_search 0) (Znth j VD_framed_search 0) (Znth j LN_framed_search 0) (Znth j LD_framed_search 0)) 1 = true) by (apply Z.eqb_eq; lia).
 rewrite HF. f_equal. apply Z.ltb_lt. lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_8_split_goal_spatial : sx_find_entering_return_wit_8_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 rewrite HA.
 assert (HL : Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite HL.
 assert (HU : Z.eqb (Znth j HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 rewrite HU. cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 cancel.
 cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_8 : sx_find_entering_return_wit_8.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_8_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_9_split_goal_1 : sx_find_entering_return_wit_9_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia | eassumption |].
 right. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
 | |- context[Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
 | |- context[Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
 end; simpl; try lia;
 match goal with H : ?r = simplex_rat_compare_flag _ _ _ _ |- _ => rewrite <- H end;
 match goal with H : ?r = 0 |- _ => rewrite H end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_9_split_goal_spatial : sx_find_entering_return_wit_9_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 assert (EA: existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA.
 assert (EL: Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EL.
 assert (EU: Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EU. cbn [andb orb negb]. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. cancel.

Qed.

Lemma proof_of_sx_find_entering_return_wit_9 : sx_find_entering_return_wit_9.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_return_wit_9_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_10_split_goal_1 : sx_find_entering_return_wit_10_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia | eassumption |].
 right. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
 | |- context[Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
 | |- context[Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
 end; simpl; try lia;
 match goal with H : ?r = simplex_rat_compare_flag _ _ _ _ |- _ => rewrite <- H end;
 match goal with H : ?r = 0 |- _ => rewrite H end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_10_split_goal_spatial : sx_find_entering_return_wit_10_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 assert (EA: existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA.
 assert (EL: Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EL.
 assert (EU: Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EU. cbn [andb orb negb]. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. cancel.

Qed.

Lemma proof_of_sx_find_entering_return_wit_10 : sx_find_entering_return_wit_10.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_return_wit_10_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_return_wit_10_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_11_split_goal_1 : sx_find_entering_return_wit_11_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia | eassumption |].
 right. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
 | |- context[Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
 | |- context[Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
 end; simpl; try lia;
 match goal with H : ?r = simplex_rat_compare_flag _ _ _ _ |- _ => rewrite <- H end;
 match goal with H : ?r = 0 |- _ => rewrite H end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_11_split_goal_spatial : sx_find_entering_return_wit_11_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 assert (EA: existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA.
 assert (EL: Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EL.
 assert (EU: Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EU. cbn [andb orb negb]. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. cancel.

Qed.

Lemma proof_of_sx_find_entering_return_wit_11 : sx_find_entering_return_wit_11.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_return_wit_11_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_return_wit_11_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_12_split_goal_1 : sx_find_entering_return_wit_12_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia | eassumption |].
 right. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
 | |- context[Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
 | |- context[Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
 end; simpl; try lia;
 match goal with H : ?r = simplex_rat_compare_flag _ _ _ _ |- _ => rewrite <- H end;
 match goal with H : ?r = 0 |- _ => rewrite H end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_12_split_goal_spatial : sx_find_entering_return_wit_12_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 assert (EA: existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA.
 assert (EL: Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EL.
 assert (EU: Z.eqb (Znth j HU_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EU. cbn [andb orb negb]. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. cancel.

Qed.

Lemma proof_of_sx_find_entering_return_wit_12 : sx_find_entering_return_wit_12.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_return_wit_12_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_return_wit_12_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_13_split_goal_1 : sx_find_entering_return_wit_13_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia | eassumption |].
 right. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
 | |- context[Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
 | |- context[Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
 end; simpl; try lia;
 match goal with H : ?r = simplex_rat_compare_flag _ _ _ _ |- _ => rewrite <- H end;
 match goal with H : ?r = 0 |- _ => rewrite H end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_13_split_goal_spatial : sx_find_entering_return_wit_13_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 assert (EA: existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA.
 assert (EL: Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EL.
 assert (EU: Z.eqb (Znth j HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 rewrite EU. cbn [andb orb negb]. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. cancel. try cancel emp.

Qed.

Lemma proof_of_sx_find_entering_return_wit_13 : sx_find_entering_return_wit_13.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_return_wit_13_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_return_wit_13_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_14_split_goal_1 : sx_find_entering_return_wit_14_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia | eassumption |].
 right. split; [reflexivity|]. split; [reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
 | |- context[Z.eqb ?x 0] => let E := fresh "E" in destruct (Z.eqb x 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
 | |- context[Z.ltb ?x ?y] => let E := fresh "E" in destruct (Z.ltb x y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
 end; simpl; try lia;
 match goal with H : ?r = simplex_rat_compare_flag _ _ _ _ |- _ => rewrite <- H end;
 match goal with H : ?r = 0 |- _ => rewrite H end; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_14_split_goal_spatial : sx_find_entering_return_wit_14_split_goal_spatial.
Proof.
LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__lower_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by ring.
 cancel (simplex_enter_num_except S_framed_search R_framed_search V_framed_search CN_framed_search j).
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 assert (EA: existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
 { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
 unfold simplex_scan_read_slot. rewrite EA.
 assert (EL: Z.eqb (Znth j HL_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
 rewrite EL.
 assert (EU: Z.eqb (Znth j HU_framed_search 0) 0 = true) by (apply Z.eqb_eq; lia).
 rewrite EU. cbn [andb orb negb]. unfold simplex_scan_rat_memory. csimpl. sepcon_right_assoc. cancel. try cancel emp.

Qed.

Lemma proof_of_sx_find_entering_return_wit_14 : sx_find_entering_return_wit_14.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_sx_find_entering_return_wit_14_split_goal_spatial.
 Goal_apply proof_of_sx_find_entering_return_wit_14_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_15_split_goal_1 : sx_find_entering_return_wit_15_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|assumption|].
 left. split;[reflexivity|]. split;[reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => let H := fresh "HE" in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try lia
 | |- context [Z.ltb ?a ?b] => let H := fresh "HE" in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try lia
 end; cbn; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_15_split_goal_spatial : sx_find_entering_return_wit_15_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
 rewrite replace_Znth_Znth.
 sep_apply_r_atomic (num_restore__unbounded_one_side S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 csimpl.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 unfold simplex_scan_read_slot.
 rewrite (active_range__unbounded_one_side j V_framed_search ltac:(lia)).
 rewrite PreH17.
 assert (EU: (Znth j HU_framed_search 0 =? 0)%Z = false) by (apply Z.eqb_neq;lia).
 rewrite EU.
 cbn beta iota zeta delta [Z.eqb negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- ?p ** _ |-- _ => cancel p end.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 match goal with |- ?p |-- _ => cancel p end.
 cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_15 : sx_find_entering_return_wit_15.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_15_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_15_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_16_split_goal_1 : sx_find_entering_return_wit_16_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|assumption|].
 left. split;[reflexivity|]. split;[reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => let H := fresh "HE" in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try lia
 | |- context [Z.ltb ?a ?b] => let H := fresh "HE" in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try lia
 end; cbn; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_16_split_goal_spatial : sx_find_entering_return_wit_16_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
 rewrite replace_Znth_Znth.
 sep_apply_r_atomic (num_restore__unbounded_one_side S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 csimpl.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 unfold simplex_scan_read_slot.
 rewrite (active_range__unbounded_one_side j V_framed_search ltac:(lia)).
 rewrite PreH17.
 assert (EU: (Znth j HU_framed_search 0 =? 0)%Z = false) by (apply Z.eqb_neq;lia).
 rewrite EU.
 cbn beta iota zeta delta [Z.eqb negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- ?p ** _ |-- _ => cancel p end.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 match goal with |- ?p |-- _ => cancel p end.
 cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_16 : sx_find_entering_return_wit_16.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_16_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_16_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_17_split_goal_1 : sx_find_entering_return_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
  left. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  rewrite PreH14, PreH31, PreH32.
  assert (HC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite HC. cbn [negb orb].
  destruct (((Z.ltb 0 (Znth j CN_framed_search 0)) && (Z.ltb 0 D_framed_search)) ||
            ((Z.ltb (Znth j CN_framed_search 0) 0) && (Z.ltb D_framed_search 0)))%bool; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_17_split_goal_spatial : sx_find_entering_return_wit_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
  rewrite replace_Znth_Znth.
  cancel (IntArray.full (&(S_framed_search # "SxState" ->ₛ "is_basic")) V_framed_search IB_framed_search).
  sep_apply_r_atomic (num_restore__exit_and_empty_slot S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell. rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel. 
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
  { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
  rewrite HA, PreH31, PreH32. cbn [Z.eqb negb andb orb]. sepcon_right_assoc.
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> 0).
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> 0).
  cancel.
  cancel emp.
  cancel emp.
  cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_17 : sx_find_entering_return_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_return_wit_17_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_return_wit_17_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_18_split_goal_1 : sx_find_entering_return_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
  left. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  rewrite PreH14, PreH31, PreH32.
  assert (HC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite HC. cbn [negb orb].
  destruct (((Z.ltb 0 (Znth j CN_framed_search 0)) && (Z.ltb 0 D_framed_search)) ||
            ((Z.ltb (Znth j CN_framed_search 0) 0) && (Z.ltb D_framed_search 0)))%bool; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_18_split_goal_spatial : sx_find_entering_return_wit_18_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
  rewrite replace_Znth_Znth.
  cancel (IntArray.full (&(S_framed_search # "SxState" ->ₛ "is_basic")) V_framed_search IB_framed_search).
  sep_apply_r_atomic (num_restore__exit_and_empty_slot S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell. rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel. 
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
  { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
  rewrite HA, PreH31, PreH32. cbn [Z.eqb negb andb orb]. sepcon_right_assoc.
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> 0).
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> 0).
  cancel.
  cancel emp.
  cancel emp.
  cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_18 : sx_find_entering_return_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_return_wit_18_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_return_wit_18_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_19_split_goal_1 : sx_find_entering_return_wit_19_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. repeat split; try reflexivity.
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_lt a b) ltac:(lia)) | rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))]
 end.
 reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_19_split_goal_spatial : sx_find_entering_return_wit_19_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__upper_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite active__upper_candidate by lia.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 end.
 cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 all: cancel.
 all: try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_return_wit_19 : sx_find_entering_return_wit_19.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_19_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_19_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_20_split_goal_1 : sx_find_entering_return_wit_20_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. repeat split; try reflexivity.
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_lt a b) ltac:(lia)) | rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))]
 end.
 reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_20_split_goal_spatial : sx_find_entering_return_wit_20_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__upper_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite active__upper_candidate by lia.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 end.
 cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 all: cancel.
 all: try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_return_wit_20 : sx_find_entering_return_wit_20.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_20_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_20_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_21_split_goal_1 : sx_find_entering_return_wit_21_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. repeat split; try reflexivity.
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_lt a b) ltac:(lia)) | rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))]
 end.
 reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_21_split_goal_spatial : sx_find_entering_return_wit_21_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__upper_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite active__upper_candidate by lia.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 end.
 cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 all: cancel.
 all: try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_return_wit_21 : sx_find_entering_return_wit_21.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_21_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_21_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_22_split_goal_1 : sx_find_entering_return_wit_22_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. repeat split; try reflexivity.
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_lt a b) ltac:(lia)) | rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))]
 end.
 reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_22_split_goal_spatial : sx_find_entering_return_wit_22_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__upper_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite active__upper_candidate by lia.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 end.
 cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 all: cancel.
 all: try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_return_wit_22 : sx_find_entering_return_wit_22.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_22_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_22_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_23_split_goal_1 : sx_find_entering_return_wit_23_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. repeat split; try reflexivity.
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_lt a b) ltac:(lia)) | rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))]
 end.
 reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_23_split_goal_spatial : sx_find_entering_return_wit_23_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__upper_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite active__upper_candidate by lia.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 end.
 cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 all: cancel.
 all: try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_return_wit_23 : sx_find_entering_return_wit_23.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_23_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_23_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_24_split_goal_1 : sx_find_entering_return_wit_24_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
 left. repeat split; try reflexivity.
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_lt a b) ltac:(lia)) | rewrite (proj2 (Z.ltb_ge a b) ltac:(lia))]
 end.
 reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_24_split_goal_spatial : sx_find_entering_return_wit_24_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply_r_atomic (num_restore__upper_candidate S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 replace (sizeof("SxRat") * 24) with (24 * sizeof("SxRat")) by lia.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
 unfold simplex_scan_read_slot.
 rewrite active__upper_candidate by lia.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => first [rewrite (proj2 (Z.eqb_eq a b) ltac:(lia)) | rewrite (proj2 (Z.eqb_neq a b) ltac:(lia))]
 end.
 cbn [andb orb negb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 all: cancel.
 all: try (cancel emp).
Qed.

Lemma proof_of_sx_find_entering_return_wit_24 : sx_find_entering_return_wit_24.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_24_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_24_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_25_split_goal_1 : sx_find_entering_return_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia | assumption |].
  right. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) eqn:?; simpl
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
  end;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; try reflexivity; try congruence; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_25_split_goal_spatial : sx_find_entering_return_wit_25_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_rejection by lia.
  repeat match goal with
  | H : Znth j ?l 0 = 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite H, Z.eqb_refl
  | H : Znth j ?l 0 <> 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end.
  cbn [andb orb negb].
  unfold simplex_scan_rat_memory. csimpl.
  sepcon_right_assoc.
  repeat match goal with
  | |- ?P ** _ |-- _ => progress cancel P
  end.
  match goal with |- ?P |-- _ => cancel P end; cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_25 : sx_find_entering_return_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_return_wit_25_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_return_wit_25_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_26_split_goal_1 : sx_find_entering_return_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia | assumption |].
  right. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) eqn:?; simpl
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
  end;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; try reflexivity; try congruence; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_26_split_goal_spatial : sx_find_entering_return_wit_26_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_rejection by lia.
  repeat match goal with
  | H : Znth j ?l 0 = 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite H, Z.eqb_refl
  | H : Znth j ?l 0 <> 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end.
  cbn [andb orb negb].
  unfold simplex_scan_rat_memory. csimpl.
  sepcon_right_assoc.
  repeat match goal with
  | |- ?P ** _ |-- _ => progress cancel P
  end.
  match goal with |- ?P |-- _ => cancel P end; cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_26 : sx_find_entering_return_wit_26.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_26_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_26_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_27_split_goal_1 : sx_find_entering_return_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia | assumption |].
  right. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) eqn:?; simpl
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
  end;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; try reflexivity; try congruence; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_27_split_goal_spatial : sx_find_entering_return_wit_27_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_rejection by lia.
  repeat match goal with
  | H : Znth j ?l 0 = 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite H, Z.eqb_refl
  | H : Znth j ?l 0 <> 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end.
  cbn [andb orb negb].
  unfold simplex_scan_rat_memory. csimpl.
  sepcon_right_assoc.
  repeat match goal with
  | |- ?P ** _ |-- _ => progress cancel P
  end.
  match goal with |- ?P |-- _ => cancel P end; cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_27 : sx_find_entering_return_wit_27.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_27_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_27_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_28_split_goal_1 : sx_find_entering_return_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia | assumption |].
  right. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) eqn:?; simpl
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
  end;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; try reflexivity; try congruence; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_28_split_goal_spatial : sx_find_entering_return_wit_28_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_rejection by lia.
  repeat match goal with
  | H : Znth j ?l 0 = 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite H, Z.eqb_refl
  | H : Znth j ?l 0 <> 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end.
  cbn [andb orb negb].
  unfold simplex_scan_rat_memory. csimpl.
  sepcon_right_assoc.
  repeat match goal with
  | |- ?P ** _ |-- _ => progress cancel P
  end.
  match goal with |- ?P |-- _ => cancel P end; cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_28 : sx_find_entering_return_wit_28.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_28_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_28_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_29_split_goal_1 : sx_find_entering_return_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia | assumption |].
  right. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) eqn:?; simpl
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
  end;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; try reflexivity; try congruence; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_29_split_goal_spatial : sx_find_entering_return_wit_29_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_rejection by lia.
  repeat match goal with
  | H : Znth j ?l 0 = 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite H, Z.eqb_refl
  | H : Znth j ?l 0 <> 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end.
  cbn [andb orb negb].
  unfold simplex_scan_rat_memory. csimpl.
  sepcon_right_assoc.
  repeat match goal with
  | |- ?P ** _ |-- _ => progress cancel P
  end.
  match goal with |- ?P |-- _ => cancel P end; cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_29 : sx_find_entering_return_wit_29.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_29_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_29_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_30_split_goal_1 : sx_find_entering_return_wit_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia | assumption |].
  right. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb x y) eqn:?; simpl
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
  end;
  repeat match goal with
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; try reflexivity; try congruence; lia.
Qed.

Lemma proof_of_sx_find_entering_return_wit_30_split_goal_spatial : sx_find_entering_return_wit_30_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_r_atomic (num_restore__upper_rejection S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell.
  rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel.
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  rewrite active__upper_rejection by lia.
  repeat match goal with
  | H : Znth j ?l 0 = 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite H, Z.eqb_refl
  | H : Znth j ?l 0 <> 0 |- context [Z.eqb (Znth j ?l 0) 0] => rewrite (proj2 (Z.eqb_neq _ _) H)
  end.
  cbn [andb orb negb].
  unfold simplex_scan_rat_memory. csimpl.
  sepcon_right_assoc.
  repeat match goal with
  | |- ?P ** _ |-- _ => progress cancel P
  end.
  match goal with |- ?P |-- _ => cancel P end; cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_30 : sx_find_entering_return_wit_30.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_30_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_30_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_31_split_goal_1 : sx_find_entering_return_wit_31_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|assumption|].
 left. split;[reflexivity|]. split;[reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => let H := fresh "HE" in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try lia
 | |- context [Z.ltb ?a ?b] => let H := fresh "HE" in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try lia
 end; cbn; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_31_split_goal_spatial : sx_find_entering_return_wit_31_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
 rewrite replace_Znth_Znth.
 sep_apply_r_atomic (num_restore__unbounded_one_side S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 csimpl.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 unfold simplex_scan_read_slot.
 rewrite (active_range__unbounded_one_side j V_framed_search ltac:(lia)).
 rewrite PreH17.
 assert (EL: (Znth j HL_framed_search 0 =? 0)%Z = false) by (apply Z.eqb_neq;lia).
 rewrite EL.
 cbn beta iota zeta delta [Z.eqb negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- ?p ** _ |-- _ => cancel p end.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 match goal with |- ?p |-- _ => cancel p end.
Qed.

Lemma proof_of_sx_find_entering_return_wit_31 : sx_find_entering_return_wit_31.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_31_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_31_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_32_split_goal_1 : sx_find_entering_return_wit_32_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 dump_pre_spatial.
 unfold simplex_find_entering_spec.
 eapply simplex_enter_finish with (k:=j); [lia|assumption|].
 left. split;[reflexivity|]. split;[reflexivity|].
 unfold simplex_enter_observations, simplex_enter_column.
 repeat match goal with
 | |- context [Z.eqb ?a ?b] => let H := fresh "HE" in destruct (Z.eqb a b) eqn:H; [apply Z.eqb_eq in H|apply Z.eqb_neq in H]; try lia
 | |- context [Z.ltb ?a ?b] => let H := fresh "HE" in destruct (Z.ltb a b) eqn:H; [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; try lia
 end; cbn; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_32_split_goal_spatial : sx_find_entering_return_wit_32_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 sep_apply (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
 rewrite replace_Znth_Znth.
 sep_apply_r_atomic (num_restore__unbounded_one_side S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
 unfold simplex_enter_num_cell.
 rewrite (Z.mul_comm (sizeof("SxRat")) 24).
 csimpl.
 cancel.
 sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
 unfold simplex_scan_read_slot.
 rewrite (active_range__unbounded_one_side j V_framed_search ltac:(lia)).
 rewrite PreH17.
 assert (EL: (Znth j HL_framed_search 0 =? 0)%Z = false) by (apply Z.eqb_neq;lia).
 rewrite EL.
 cbn beta iota zeta delta [Z.eqb negb andb orb].
 unfold simplex_scan_rat_memory.
 csimpl.
 sepcon_right_assoc.
 repeat match goal with |- ?p ** _ |-- _ => cancel p end.
 repeat match goal with |- _ |-- ?p ** _ => cancel p end.
 match goal with |- ?p |-- _ => cancel p end.
Qed.

Lemma proof_of_sx_find_entering_return_wit_32 : sx_find_entering_return_wit_32.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_sx_find_entering_return_wit_32_split_goal_spatial.
 - Goal_apply proof_of_sx_find_entering_return_wit_32_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_33_split_goal_1 : sx_find_entering_return_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
  left. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  rewrite PreH14, PreH31, PreH32.
  assert (HC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite HC. cbn [negb orb].
  destruct (((Z.ltb 0 (Znth j CN_framed_search 0)) && (Z.ltb 0 D_framed_search)) ||
            ((Z.ltb (Znth j CN_framed_search 0) 0) && (Z.ltb D_framed_search 0)))%bool; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_33_split_goal_spatial : sx_find_entering_return_wit_33_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
  rewrite replace_Znth_Znth.
  cancel (IntArray.full (&(S_framed_search # "SxState" ->ₛ "is_basic")) V_framed_search IB_framed_search).
  sep_apply_r_atomic (num_restore__exit_and_empty_slot S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell. rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel. 
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
  { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
  rewrite HA, PreH31, PreH32. cbn [Z.eqb negb andb orb]. sepcon_right_assoc.
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> 0).
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> 0).
  cancel.
  cancel emp.
  cancel emp.
  cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_33 : sx_find_entering_return_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_return_wit_33_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_return_wit_33_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_return_wit_34_split_goal_1 : sx_find_entering_return_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold simplex_find_entering_spec.
  eapply simplex_enter_finish with (k:=j); [lia|eassumption|].
  left. split; [reflexivity|]. split; [reflexivity|].
  unfold simplex_enter_observations, simplex_enter_column.
  rewrite PreH13, PreH30, PreH31.
  assert (HC : Z.eqb (Znth j CN_framed_search 0) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite HC. cbn [negb orb].
  destruct (((Z.ltb 0 (Znth j CN_framed_search 0)) && (Z.ltb 0 D_framed_search)) ||
            ((Z.ltb (Znth j CN_framed_search 0) 0) && (Z.ltb D_framed_search 0)))%bool; reflexivity.
Qed.

Lemma proof_of_sx_find_entering_return_wit_34_split_goal_spatial : sx_find_entering_return_wit_34_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full (&(S_framed_search # "SxState" ->ₛ "is_basic")) j V_framed_search (Znth j IB_framed_search 0) IB_framed_search ltac:(lia)).
  rewrite replace_Znth_Znth.
  cancel (IntArray.full (&(S_framed_search # "SxState" ->ₛ "is_basic")) V_framed_search IB_framed_search).
  sep_apply_r_atomic (num_restore__exit_and_empty_slot S_framed_search R_framed_search V_framed_search CN_framed_search j ltac:(lia)).
  unfold simplex_enter_num_cell. rewrite (Z.mul_comm (sizeof("SxRat")) 24).
  cancel. 
  sep_apply_r_atomic (read_slot_merge__upper_update S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j ltac:(lia)).
  cancel (simplex_scan_read_except S_framed_search (Zrange 0 V_framed_search) HL_framed_search HU_framed_search VN_framed_search VD_framed_search LN_framed_search LD_framed_search UN_framed_search UD_framed_search j).
  unfold simplex_scan_read_slot.
  assert (HA : existsb (Z.eqb j) (Zrange 0 V_framed_search) = true).
  { apply existsb_exists. exists j. split; [apply In_Zrange; lia|apply Z.eqb_refl]. }
  rewrite HA, PreH30, PreH31. cbn [Z.eqb negb andb orb]. sepcon_right_assoc.
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_lower") + j * sizeof(INT)) # Int |-> 0).
  cancel ((&(S_framed_search # "SxState" ->ₛ "has_upper") + j * sizeof(INT)) # Int |-> 0).
  cancel.
  cancel emp.
  cancel emp.
  cancel emp.
Qed.

Lemma proof_of_sx_find_entering_return_wit_34 : sx_find_entering_return_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_return_wit_34_split_goal_spatial.
  - Goal_apply proof_of_sx_find_entering_return_wit_34_split_goal_1.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_1_pure_split_goal_1 : sx_find_entering_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) VD_framed_search |- _ =>
      apply (proj1 (Forall_forall _ _) H)
  end.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_1_pure_split_goal_2 : sx_find_entering_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> _ /\ Znth i UD_framed_search 0 <= INT_MAX |- _ =>
      pose proof (H j ltac:(repeat split; assumption)) as Hupper
  end.
  tauto.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_1_pure : sx_find_entering_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_2_pure_split_goal_1 : sx_find_entering_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) VD_framed_search |- _ =>
      apply (proj1 (Forall_forall _ _) H)
  end.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_2_pure_split_goal_2 : sx_find_entering_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> _ /\ Znth i UD_framed_search 0 <= INT_MAX |- _ =>
      pose proof (H j ltac:(repeat split; assumption)) as Hupper
  end.
  tauto.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_2_pure : sx_find_entering_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_2_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_3_pure_split_goal_1 : sx_find_entering_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) VD_framed_search |- _ =>
      apply (proj1 (Forall_forall _ _) H)
  end.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_3_pure_split_goal_2 : sx_find_entering_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> _ /\ Znth i UD_framed_search 0 <= INT_MAX |- _ =>
      pose proof (H j ltac:(repeat split; assumption)) as Hupper
  end.
  tauto.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_3_pure : sx_find_entering_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_4_pure_split_goal_1 : sx_find_entering_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) VD_framed_search |- _ =>
      apply (proj1 (Forall_forall _ _) H)
  end.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_4_pure_split_goal_2 : sx_find_entering_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> _ /\ Znth i UD_framed_search 0 <= INT_MAX |- _ =>
      pose proof (H j ltac:(repeat split; assumption)) as Hupper
  end.
  tauto.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_4_pure : sx_find_entering_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_4_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_5_pure_split_goal_1 : sx_find_entering_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) VD_framed_search |- _ =>
      apply (proj1 (Forall_forall _ _) H)
  end.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_5_pure_split_goal_2 : sx_find_entering_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> _ /\ Znth i UD_framed_search 0 <= INT_MAX |- _ =>
      pose proof (H j ltac:(repeat split; assumption)) as Hupper
  end.
  tauto.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_5_pure : sx_find_entering_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_6_pure_split_goal_1 : sx_find_entering_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : Forall (Z.le 1) VD_framed_search |- _ =>
      apply (proj1 (Forall_forall _ _) H)
  end.
  unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. rewrite Zlength_correct in *. lia.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_6_pure_split_goal_2 : sx_find_entering_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> _ /\ Znth i UD_framed_search 0 <= INT_MAX |- _ =>
      pose proof (H j ltac:(repeat split; assumption)) as Hupper
  end.
  tauto.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_6_pure : sx_find_entering_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_7_pure_split_goal_1 : sx_find_entering_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply Forall_Znth_Zlength; [eassumption | lia].
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_7_pure_split_goal_2 : sx_find_entering_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i LD_framed_search 0)) /\ _) |- _ =>
    specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_7_pure : sx_find_entering_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_8_pure_split_goal_1 : sx_find_entering_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply Forall_Znth_Zlength; [eassumption | lia].
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_8_pure_split_goal_2 : sx_find_entering_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i LD_framed_search 0)) /\ _) |- _ =>
    specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_8_pure : sx_find_entering_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_9_pure_split_goal_1 : sx_find_entering_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply Forall_Znth_Zlength; [eassumption | lia].
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_9_pure_split_goal_2 : sx_find_entering_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i LD_framed_search 0)) /\ _) |- _ =>
    specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_9_pure : sx_find_entering_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_9_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_10_pure_split_goal_1 : sx_find_entering_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply Forall_Znth_Zlength; [eassumption | lia].
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_10_pure_split_goal_2 : sx_find_entering_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i LD_framed_search 0)) /\ _) |- _ =>
    specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_10_pure : sx_find_entering_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_10_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_11_pure_split_goal_1 : sx_find_entering_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply Forall_Znth_Zlength; [eassumption | lia].
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_11_pure_split_goal_2 : sx_find_entering_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i LD_framed_search 0)) /\ _) |- _ =>
    specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_11_pure : sx_find_entering_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_11_pure_split_goal_2.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_12_pure_split_goal_1 : sx_find_entering_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  eapply Forall_Znth_Zlength; [eassumption | lia].
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_12_pure_split_goal_2 : sx_find_entering_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with
  | H : forall i : Z, _ -> ((_ /\ (1 <= Znth i LD_framed_search 0)) /\ _) |- _ =>
    specialize (H j ltac:(repeat split; assumption)); tauto
  end.
Qed.

Lemma proof_of_sx_find_entering_partial_solve_wit_12_pure : sx_find_entering_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_12_pure_split_goal_1.
  - Goal_apply proof_of_sx_find_entering_partial_solve_wit_12_pure_split_goal_2.
Qed.

