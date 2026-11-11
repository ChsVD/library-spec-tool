(** Shared record logic generated from [AFPoint] and [JPoint]. *)
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

From SimpleC.EE.Applications_human.sm2.lib Require Export u32_def.

Record RecordJPoint : Type := make_record_jpoint {
  JPoint_x : Recordu32;
  JPoint_y : Recordu32;
  JPoint_z : Recordu32
}.

Definition zero_record_jpoint : RecordJPoint :=
  make_record_jpoint zero_record_u32 zero_record_u32 zero_record_u32.

Definition StructPredJPoint (x : Z) (v : RecordJPoint) : Assertion :=
  (StructPredu32 (&(x # "JPoint" ->ₛ "x")) v.(JPoint_x)) **
  (StructPredu32 (&(x # "JPoint" ->ₛ "y")) v.(JPoint_y)) **
  (StructPredu32 (&(x # "JPoint" ->ₛ "z")) v.(JPoint_z)).

Definition UndefStructPredJPoint (x : Z) : Assertion :=
  (UndefStructPredu32 (&(x # "JPoint" ->ₛ "x"))) **
  (UndefStructPredu32 (&(x # "JPoint" ->ₛ "y"))) **
  (UndefStructPredu32 (&(x # "JPoint" ->ₛ "z"))).

Lemma store_PredJPoint_to_undef : forall x v,
  StructPredJPoint x v |-- UndefStructPredJPoint x.
Proof.
  intros.
  unfold StructPredJPoint, UndefStructPredJPoint.
  sep_apply store_Predu32_to_undef.
  sep_apply store_Predu32_to_undef.
  sep_apply store_Predu32_to_undef.
  cancel.
Qed.

Lemma undefstore_PredJPoint_to_align : forall x,
  UndefStructPredJPoint x |-- store_align_n (((0 + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA).
Proof.
  intros.
  unfold UndefStructPredJPoint.
  sep_apply undefstore_Predu32_to_align.
  sep_apply undefstore_Predu32_to_align.
  sep_apply undefstore_Predu32_to_align.
  unfold StoreStructu32AsElement.sizeA.
  rewrite sizeof_uint64.
  change
    ((store_align_n 32 ** (store_align_n 32 ** store_align_n 32))
      |-- store_align_n 96).
  sep_apply (store_align_merge 32 32).
  exact (store_align_merge 64 32).
Qed.

Lemma store_PredJPoint_to_align : forall x v,
  StructPredJPoint x v |-- store_align_n (((0 + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA).
Proof.
  intros.
  sep_apply store_PredJPoint_to_undef.
  sep_apply undefstore_PredJPoint_to_align.
  cancel.
Qed.

Module StoreStructJPointAsElement <: ELEMENT_STORE.
  Definition A := RecordJPoint.
  Definition sizeA := (((0 + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA).
  Definition storeA (x: addr) (lo: Z) (a: RecordJPoint): Assertion :=
    (StructPredJPoint (x + lo * sizeA) a).
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (UndefStructPredJPoint (x + lo * sizeA)).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_PredJPoint_to_undef.
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
    sep_apply store_PredJPoint_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_PredJPoint_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
  unfold StoreStructu32AsElement.sizeA.
  try rewrite sizeof_uint64.
  unfold StoreStructu32AsElement.sizeA.
  try rewrite sizeof_uint64.
  unfold StoreStructu32AsElement.sizeA.
  try rewrite sizeof_uint64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreStructJPointAsElement.

Module StructJPointArray := ArrayLib (StoreStructJPointAsElement).

Record RecordAFPoint : Type := make_record_afpoint {
  AFPoint_x : Recordu32;
  AFPoint_y : Recordu32
}.

Definition zero_record_afpoint : RecordAFPoint :=
  make_record_afpoint zero_record_u32 zero_record_u32.

Definition StructPredAFPoint (x : Z) (v : RecordAFPoint) : Assertion :=
  (StructPredu32 (&(x # "AFPoint" ->ₛ "x")) v.(AFPoint_x)) **
  (StructPredu32 (&(x # "AFPoint" ->ₛ "y")) v.(AFPoint_y)).

Definition UndefStructPredAFPoint (x : Z) : Assertion :=
  (UndefStructPredu32 (&(x # "AFPoint" ->ₛ "x"))) **
  (UndefStructPredu32 (&(x # "AFPoint" ->ₛ "y"))).

Lemma store_PredAFPoint_to_undef : forall x v,
  StructPredAFPoint x v |-- UndefStructPredAFPoint x.
Proof.
  intros.
  unfold StructPredAFPoint, UndefStructPredAFPoint.
  sep_apply store_Predu32_to_undef.
  sep_apply store_Predu32_to_undef.
  cancel.
Qed.

Lemma undefstore_PredAFPoint_to_align : forall x,
  UndefStructPredAFPoint x |-- store_align_n ((0 + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA).
Proof.
  intros.
  unfold UndefStructPredAFPoint.
  sep_apply undefstore_Predu32_to_align.
  sep_apply undefstore_Predu32_to_align.
  unfold StoreStructu32AsElement.sizeA.
  rewrite sizeof_uint64.
  change ((store_align_n 32 ** store_align_n 32) |-- store_align_n 64).
  exact (store_align_merge 32 32).
Qed.

Lemma store_PredAFPoint_to_align : forall x v,
  StructPredAFPoint x v |-- store_align_n ((0 + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA).
Proof.
  intros.
  sep_apply store_PredAFPoint_to_undef.
  sep_apply undefstore_PredAFPoint_to_align.
  cancel.
Qed.

Module StoreStructAFPointAsElement <: ELEMENT_STORE.
  Definition A := RecordAFPoint.
  Definition sizeA := ((0 + StoreStructu32AsElement.sizeA) + StoreStructu32AsElement.sizeA).
  Definition storeA (x: addr) (lo: Z) (a: RecordAFPoint): Assertion :=
    (StructPredAFPoint (x + lo * sizeA) a).
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (UndefStructPredAFPoint (x + lo * sizeA)).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_PredAFPoint_to_undef.
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
    sep_apply store_PredAFPoint_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_PredAFPoint_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
  unfold StoreStructu32AsElement.sizeA.
  try rewrite sizeof_uint64.
  unfold StoreStructu32AsElement.sizeA.
  try rewrite sizeof_uint64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.

End StoreStructAFPointAsElement.

Module StructAFPointArray := ArrayLib (StoreStructAFPointAsElement).
