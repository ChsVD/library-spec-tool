From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_lib.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

(* A canonical positive one-limb magnitude is exactly its readable limb. *)
Lemma combine_single_limb_open p z :
  mpd_store_Z_compact UINT_MOD p z 1 |--
    “ 1 <= z < UINT_MOD ” && UIntArray.full p 1 [z].
Proof.
  unfold mpd_store_Z_compact.
  Intros data.
  assert (Hsingle : exists limb, data = [limb]).
  { destruct data as [|limb [|next tail]].
    - rewrite Zlength_nil in *. lia.
    - eauto.
    - repeat rewrite Zlength_cons in *.
      pose proof (Zlength_nonneg tail). lia. }
  destruct Hsingle as [limb ->].
  match goal with
  | H : list_to_Z UINT_MOD [limb] = z /\ _ |- _ =>
      destruct H as [Hval [Hhigh Hbounds]]
  end.
  rewrite list_to_Z_single in Hval.
  subst z.
  simpl in Hhigh, Hbounds.
  unfold mpd_store_list.
  rewrite Zlength_cons, Zlength_nil in *.
  change (Z.succ 0) with 1 in *.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. lia.
Qed.

(* Restore the compact magnitude after reading the one limb. *)
Lemma combine_single_limb_close p z :
  1 <= z < UINT_MOD ->
  UIntArray.full p 1 [z] |-- mpd_store_Z_compact UINT_MOD p z 1.
Proof.
  intros Hz.
  unfold mpd_store_Z_compact.
  Exists [z].
  unfold mpd_store_list.
  rewrite Zlength_cons, Zlength_nil.
  change (Z.succ 0) with 1 in *.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; rewrite ?list_to_Z_single; simpl; lia.
Qed.
