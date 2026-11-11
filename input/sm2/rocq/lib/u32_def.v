Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import Snaive_C_Rules.
Local Open Scope sac.

(** Logical representation generated for the named C structure [u32]. *)

Record Recordu32 : Type := make_record_u32 {
  u32_v : list Z
}.

Definition zero_record_u32 : Recordu32 :=
  make_record_u32 (repeat_Z 0 4).

Definition StructPredu32 (x : Z) (v : Recordu32) : Assertion :=
  (UInt64Array.full (&(x # "u32" ->ₛ "v")) 4 v.(u32_v)).

Definition UndefStructPredu32 (x : Z) : Assertion :=
  (UInt64Array.undef_full (&(x # "u32" ->ₛ "v")) 4).

Lemma store_Predu32_to_undef : forall x v,
  StructPredu32 x v |-- UndefStructPredu32 x.
Proof.
  intros.
  unfold StructPredu32, UndefStructPredu32.
  sep_apply UInt64Array.full_to_undef_full.
  cancel.
Qed.

Lemma undefstore_Predu32_to_align : forall x,
  UndefStructPredu32 x |-- store_align_n (0 + (4 * sizeof(UINT64))).
Proof.
  intros.
  unfold UndefStructPredu32.
  sep_apply UInt64Array.undef_full_to_align.
  entailer!.
Qed.

Lemma store_Predu32_to_align : forall x v,
  StructPredu32 x v |-- store_align_n (0 + (4 * sizeof(UINT64))).
Proof.
  intros.
  sep_apply store_Predu32_to_undef.
  sep_apply undefstore_Predu32_to_align.
  cancel.
Qed.

Module StoreStructu32AsElement <: ELEMENT_STORE.
  Definition A := Recordu32.
  Definition sizeA := (0 + (4 * sizeof(UINT64))).
  Definition storeA (x: addr) (lo: Z) (a: Recordu32): Assertion :=
    (StructPredu32 (x + lo * sizeA) a).
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (UndefStructPredu32 (x + lo * sizeA)).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_Predu32_to_undef.
    cancel.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA.
    replace (x + n * sizeA + lo * sizeA) with (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA.
    replace (x + n * sizeA + lo * sizeA) with (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    sep_apply store_Predu32_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_Predu32_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    try rewrite sizeof_uint64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreStructu32AsElement.

Module Structu32Array := ArrayLib (StoreStructu32AsElement).
