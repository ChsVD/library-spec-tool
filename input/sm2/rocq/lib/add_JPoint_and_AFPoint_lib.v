Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import Snaive_C_Rules.
From SimpleC.EE.Applications_human.sm2.lib Require Export ecc.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(** Implementation-only postcondition for mixed addition.  Identity branches
    preserve the distinguished infinity encoding; the generic formula may
    produce a noncanonical [z = 0] when two finite inputs are inverses. *)
Definition store_mixed_add_result_impl
    (address : addr) (left right : ec_point) : Assertion :=
  if sm2_ec_point_dec left ECInfinity then
    store_jpoint_with_canonical_infinity
      address (sm2_point_add left right)
  else if sm2_ec_point_dec right ECInfinity then
    store_jpoint_with_canonical_infinity
      address (sm2_point_add left right)
  else
    store_jpoint address (sm2_point_add left right).

Lemma store_mixed_add_result_impl_forget :
  forall address left right,
    store_mixed_add_result_impl address left right |--
    store_jpoint address (sm2_point_add left right).
Proof.
  intros address left right.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec left ECInfinity);
    [apply store_jpoint_with_canonical_infinity_forget |].
  destruct (sm2_ec_point_dec right ECInfinity);
    [apply store_jpoint_with_canonical_infinity_forget |].
  entailer!.
Qed.

Lemma store_mixed_add_result_impl_is_canonical :
  forall address left right,
    (left = ECInfinity \/ right = ECInfinity \/
     sm2_point_add left right <> ECInfinity) ->
    store_mixed_add_result_impl address left right |--
    store_jpoint_with_canonical_infinity
      address (sm2_point_add left right).
Proof.
  intros address left right Hcanonical.
  unfold store_mixed_add_result_impl.
  destruct (sm2_ec_point_dec left ECInfinity) as [|Hleft].
  - entailer!.
  - destruct (sm2_ec_point_dec right ECInfinity) as [|Hright].
    + entailer!.
    + apply store_jpoint_noninfinity_is_canonical.
      tauto.
Qed.
