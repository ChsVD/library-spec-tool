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
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_shl_goal.
From SimpleC.EE.Applications_human.sm2.vc.basicOp Require Import u32_shl_proof_auto.
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
Local Open Scope sac.

Lemma proof_of_u32_shl_return_wit_1_split_goal_1 : u32_shl_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_2 : u32_shl_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_3 : u32_shl_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_4 : u32_shl_return_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_5 : u32_shl_return_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_6 : u32_shl_return_wit_1_split_goal_6.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_7 : u32_shl_return_wit_1_split_goal_7.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_8 : u32_shl_return_wit_1_split_goal_8.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1_split_goal_9 : u32_shl_return_wit_1_split_goal_9.
Proof. Abort.

Lemma proof_of_u32_shl_return_wit_1 : u32_shl_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  set (c0 := Z.shiftr x0 63).
  set (c1 := Z.shiftr x1 63).
  set (c2 := Z.shiftr x2 63).
  set (c3 := Z.shiftr x3 63).
  set (l0 := unsigned_last_nbits (Z.shiftl x0 1) 64).
  set (l1 := unsigned_last_nbits (Z.shiftl x1 1) 64).
  set (l2 := unsigned_last_nbits (Z.shiftl x2 1) 64).
  set (l3 := unsigned_last_nbits (Z.shiftl x3 1) 64).
  set (y0 := l0).
  set (y1 := Z.lor l1 c0).
  set (y2 := Z.lor l2 c1).
  set (y3 := Z.lor l3 c2).
  pose proof (u64_shift_components__shl_arithmetic x0
    ltac:(lia)) as Hs0.
  pose proof (u64_shift_components__shl_arithmetic x1
    ltac:(lia)) as Hs1.
  pose proof (u64_shift_components__shl_arithmetic x2
    ltac:(lia)) as Hs2.
  pose proof (u64_shift_components__shl_arithmetic x3
    ltac:(lia)) as Hs3.
  cbn zeta in Hs0, Hs1, Hs2, Hs3.
  fold l0 c0 in Hs0; fold l1 c1 in Hs1.
  fold l2 c2 in Hs2; fold l3 c3 in Hs3.
  destruct Hs0 as [Hl0 [Hc0 [Heq0 Hland0]]].
  destruct Hs1 as [Hl1 [Hc1 [Heq1 Hland1]]].
  destruct Hs2 as [Hl2 [Hc2 [Heq2 Hland2]]].
  destruct Hs3 as [Hl3 [Hc3 [Heq3 Hland3]]].
  assert (Hy1eq : y1 = l1 + c0).
  { unfold y1; apply lor_low_carry__shl_arithmetic; assumption. }
  assert (Hy2eq : y2 = l2 + c1).
  { unfold y2; apply lor_low_carry__shl_arithmetic; assumption. }
  assert (Hy3eq : y3 = l3 + c2).
  { unfold y3; apply lor_low_carry__shl_arithmetic; assumption. }
  assert (Hy0 : 0 <= y0 < U64_MOD) by
    (unfold y0; lia).
  assert (Hy1 : 0 <= y1 < U64_MOD) by lia.
  assert (Hy2 : 0 <= y2 < U64_MOD) by lia.
  assert (Hy3 : 0 <= y3 < U64_MOD) by lia.
  assert (Hcarry : unsigned_last_nbits c3 8 = c3).
  { apply unsigned_last_nbits_eq. change (0 <= c3 < 256). lia. }
  assert (Hresult :
    u256_shl_result X (u256_of_limbs y0 y1 y2 y3) c3).
  {
    unfold u256_shl_result.
    split.
    - rewrite PreH1.
      apply u256_of_limbs_range; lia.
    - split.
      + apply u256_of_limbs_range; lia.
      + split.
        * exact Hc3.
        * rewrite PreH1.
          unfold y0.
          rewrite Hy1eq, Hy2eq, Hy3eq.
          cbv [u256_of_limbs U64_MOD U256_MOD] in *.
          lia.
  }
  Exists (u256_of_limbs y0 y1 y2 y3).
  unfold store_u256, store_u256_limbs.
  Exists y0 y1 y2 y3.
  rewrite Hcarry.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hresult.
    + dump_pre_spatial.
      repeat split; try lia; reflexivity.
Qed. 
