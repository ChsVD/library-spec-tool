(** Shared record logic generated from [SM2SIG] and [PrivKey]. *)
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

Record RecordSM2SIG : Type := make_record_sm2sig {
  SM2SIG_r : Recordu32;
  SM2SIG_s : Recordu32
}.

Definition zero_record_sm2sig : RecordSM2SIG :=
  make_record_sm2sig zero_record_u32 zero_record_u32.

Definition StructPredSM2SIG (x : Z) (v : RecordSM2SIG) : Assertion :=
  (StructPredu32 (&(x # "SM2SIG" ->ₛ "r")) v.(SM2SIG_r)) **
  (StructPredu32 (&(x # "SM2SIG" ->ₛ "s")) v.(SM2SIG_s)).

Definition UndefStructPredSM2SIG (x : Z) : Assertion :=
  (UndefStructPredu32 (&(x # "SM2SIG" ->ₛ "r"))) **
  (UndefStructPredu32 (&(x # "SM2SIG" ->ₛ "s"))).

Lemma store_PredSM2SIG_to_undef : forall x v,
  StructPredSM2SIG x v |-- UndefStructPredSM2SIG x.
Proof.
  intros.
  unfold StructPredSM2SIG, UndefStructPredSM2SIG.
  sep_apply store_Predu32_to_undef.
  sep_apply store_Predu32_to_undef.
  cancel.
Qed.

Lemma undefstore_PredSM2SIG_to_align : forall x,
  UndefStructPredSM2SIG x |--
    store_align_n
      ((0 + StoreStructu32AsElement.sizeA) +
       StoreStructu32AsElement.sizeA).
Proof.
  intros.
  unfold UndefStructPredSM2SIG.
  sep_apply undefstore_Predu32_to_align.
  sep_apply undefstore_Predu32_to_align.
  unfold StoreStructu32AsElement.sizeA.
  rewrite sizeof_uint64.
  change ((store_align_n 32 ** store_align_n 32) |-- store_align_n 64).
  exact (store_align_merge 32 32).
Qed.

Lemma store_PredSM2SIG_to_align : forall x v,
  StructPredSM2SIG x v |--
    store_align_n
      ((0 + StoreStructu32AsElement.sizeA) +
       StoreStructu32AsElement.sizeA).
Proof.
  intros.
  sep_apply store_PredSM2SIG_to_undef.
  sep_apply undefstore_PredSM2SIG_to_align.
  cancel.
Qed.

Module StoreStructSM2SIGAsElement <: ELEMENT_STORE.
  Definition A := RecordSM2SIG.
  Definition sizeA :=
    ((0 + StoreStructu32AsElement.sizeA) +
     StoreStructu32AsElement.sizeA).
  Definition storeA (x : addr) (lo : Z) (a : RecordSM2SIG) : Assertion :=
    StructPredSM2SIG (x + lo * sizeA) a.
  Definition undefstoreA (x : addr) (lo : Z) : Assertion :=
    UndefStructPredSM2SIG (x + lo * sizeA).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_PredSM2SIG_to_undef.
    cancel.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA.
    replace (x + n * sizeA + lo * sizeA) with
      (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA.
    replace (x + n * sizeA + lo * sizeA) with
      (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma store_to_align : forall x lo a,
    storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    sep_apply store_PredSM2SIG_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo,
    undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_PredSM2SIG_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA, StoreStructu32AsElement.sizeA.
    rewrite sizeof_uint64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.
End StoreStructSM2SIGAsElement.

Module StructSM2SIGArray := ArrayLib (StoreStructSM2SIGAsElement).

Record RecordPrivKey : Type := make_record_privkey {
  PrivKey_da : Recordu32
}.

Definition zero_record_privkey : RecordPrivKey :=
  make_record_privkey zero_record_u32.

Definition StructPredPrivKey (x : Z) (v : RecordPrivKey) : Assertion :=
  StructPredu32 (&(x # "PrivKey" ->ₛ "da")) v.(PrivKey_da).

Definition UndefStructPredPrivKey (x : Z) : Assertion :=
  UndefStructPredu32 (&(x # "PrivKey" ->ₛ "da")).

Lemma store_PredPrivKey_to_undef : forall x v,
  StructPredPrivKey x v |-- UndefStructPredPrivKey x.
Proof.
  intros.
  unfold StructPredPrivKey, UndefStructPredPrivKey.
  apply store_Predu32_to_undef.
Qed.

Lemma undefstore_PredPrivKey_to_align : forall x,
  UndefStructPredPrivKey x |--
    store_align_n (0 + StoreStructu32AsElement.sizeA).
Proof.
  intros.
  unfold UndefStructPredPrivKey, StoreStructu32AsElement.sizeA.
  apply undefstore_Predu32_to_align.
Qed.

Lemma store_PredPrivKey_to_align : forall x v,
  StructPredPrivKey x v |--
    store_align_n (0 + StoreStructu32AsElement.sizeA).
Proof.
  intros.
  sep_apply store_PredPrivKey_to_undef.
  sep_apply undefstore_PredPrivKey_to_align.
  cancel.
Qed.

Module StoreStructPrivKeyAsElement <: ELEMENT_STORE.
  Definition A := RecordPrivKey.
  Definition sizeA := 0 + StoreStructu32AsElement.sizeA.
  Definition storeA (x : addr) (lo : Z) (a : RecordPrivKey) : Assertion :=
    StructPredPrivKey (x + lo * sizeA) a.
  Definition undefstoreA (x : addr) (lo : Z) : Assertion :=
    UndefStructPredPrivKey (x + lo * sizeA).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_PredPrivKey_to_undef.
    cancel.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA.
    replace (x + n * sizeA + lo * sizeA) with
      (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA.
    replace (x + n * sizeA + lo * sizeA) with
      (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma store_to_align : forall x lo a,
    storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    sep_apply store_PredPrivKey_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo,
    undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_PredPrivKey_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA, StoreStructu32AsElement.sizeA.
    rewrite sizeof_uint64.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.
End StoreStructPrivKeyAsElement.

Module StructPrivKeyArray := ArrayLib (StoreStructPrivKeyAsElement).
