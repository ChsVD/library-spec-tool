Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition sm2_constants_strategy10 :=
  TT &&
  emp **
  ((store_sm2_p))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_p))
  ).

Definition sm2_constants_strategy20 :=
  TT &&
  emp **
  ((store_sm2_n))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_n))
  ).

Definition sm2_constants_strategy30 :=
  TT &&
  emp **
  ((store_sm2_rhop))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_rhop))
  ).

Definition sm2_constants_strategy40 :=
  TT &&
  emp **
  ((store_sm2_rhon))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_rhon))
  ).

Definition sm2_constants_strategy50 :=
  TT &&
  emp **
  ((store_sm2_neg_inv_n))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_neg_inv_n))
  ).

Definition sm2_constants_strategy53 :=
  forall (x : Z),
    TT &&
    emp **
    ((poly_store FET_uint64  &("SM2_neg_invN")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_NEG_INV_N)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_neg_inv_n))
    ).

Definition sm2_constants_strategy60 :=
  TT &&
  emp **
  ((store_sm2_h))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_h))
  ).

Definition sm2_constants_strategy70 :=
  TT &&
  emp **
  ((store_sm2_nh))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_nh))
  ).

Definition sm2_constants_strategy92 :=
  TT &&
  emp **
  ((UInt64Array.full &( (( &("SM2_P") )) # "u32" ->ₛ "v") 4 (@cons Z ( SM2_P_LIMB_0) (@cons Z ( SM2_P_LIMB_1) (@cons Z ( SM2_P_LIMB_2) (@cons Z ( SM2_P_LIMB_3) (@nil Z)))))))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_p))
  ).

Definition sm2_constants_strategy93 :=
  TT &&
  emp **
  ((UInt64Array.full &( (( &("SM2_N") )) # "u32" ->ₛ "v") 4 (@cons Z ( SM2_N0_Z) (@cons Z ( SM2_N1_Z) (@cons Z ( SM2_N2_Z) (@cons Z ( SM2_N3_Z) (@nil Z)))))))
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp **
  ((store_sm2_n))
  ).

Definition sm2_constants_strategy11 :=
  TT &&
  emp **
  ((store_sm2_p))
  |--
  (
  TT &&
  emp **
  ((UInt64Array.full &( (( &("SM2_P") )) # "u32" ->ₛ "v") 4 (@cons Z ( SM2_P_LIMB_0) (@cons Z ( SM2_P_LIMB_1) (@cons Z ( SM2_P_LIMB_2) (@cons Z ( SM2_P_LIMB_3) (@nil Z)))))))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy21 :=
  TT &&
  emp **
  ((store_sm2_n))
  |--
  (
  TT &&
  emp **
  ((UInt64Array.full &( (( &("SM2_N") )) # "u32" ->ₛ "v") 4 (@cons Z ( SM2_N0_Z) (@cons Z ( SM2_N1_Z) (@cons Z ( SM2_N2_Z) (@cons Z ( SM2_N3_Z) (@nil Z)))))))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy31 :=
  TT &&
  emp **
  ((store_sm2_rhop))
  |--
  (
  TT &&
  emp **
  ((store_u256  &("SM2_rhoP")  ( SM2_RHOP_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy41 :=
  TT &&
  emp **
  ((store_sm2_rhon))
  |--
  (
  TT &&
  emp **
  ((store_u256  &("SM2_rhoN")  ( SM2_RHON_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy51 :=
  TT &&
  emp **
  ((store_sm2_neg_inv_n))
  |--
  (
  TT &&
  emp **
  ((poly_store FET_uint64  &("SM2_neg_invN")  ( SM2_NEG_INV_N)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy61 :=
  TT &&
  emp **
  ((store_sm2_h))
  |--
  (
  TT &&
  emp **
  ((store_u256  &("SM2_H")  ( SM2_H_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy71 :=
  TT &&
  emp **
  ((store_sm2_nh))
  |--
  (
  TT &&
  emp **
  ((store_fn  &("SM2_NH")  ( SM2_NH_Z)))
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition sm2_constants_strategy81 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_u256  &("SM2_P")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_P_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_p))
    ).

Definition sm2_constants_strategy83 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_u256  &("SM2_N")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_N_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_n))
    ).

Definition sm2_constants_strategy85 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_u256  &("SM2_rhoP")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_RHOP_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_rhop))
    ).

Definition sm2_constants_strategy87 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_u256  &("SM2_rhoN")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_RHON_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_rhon))
    ).

Definition sm2_constants_strategy89 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_u256  &("SM2_H")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_H_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_h))
    ).

Definition sm2_constants_strategy91 :=
  forall (x : Z),
    TT &&
    emp **
    ((store_fn  &("SM2_NH")  x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (x = ( SM2_NH_Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((store_sm2_nh))
    ).

Module Type sm2_constants_Strategy_Correct.

  Axiom sm2_constants_strategy10_correctness : sm2_constants_strategy10.
  Axiom sm2_constants_strategy20_correctness : sm2_constants_strategy20.
  Axiom sm2_constants_strategy30_correctness : sm2_constants_strategy30.
  Axiom sm2_constants_strategy40_correctness : sm2_constants_strategy40.
  Axiom sm2_constants_strategy50_correctness : sm2_constants_strategy50.
  Axiom sm2_constants_strategy53_correctness : sm2_constants_strategy53.
  Axiom sm2_constants_strategy60_correctness : sm2_constants_strategy60.
  Axiom sm2_constants_strategy70_correctness : sm2_constants_strategy70.
  Axiom sm2_constants_strategy92_correctness : sm2_constants_strategy92.
  Axiom sm2_constants_strategy93_correctness : sm2_constants_strategy93.
  Axiom sm2_constants_strategy11_correctness : sm2_constants_strategy11.
  Axiom sm2_constants_strategy21_correctness : sm2_constants_strategy21.
  Axiom sm2_constants_strategy31_correctness : sm2_constants_strategy31.
  Axiom sm2_constants_strategy41_correctness : sm2_constants_strategy41.
  Axiom sm2_constants_strategy51_correctness : sm2_constants_strategy51.
  Axiom sm2_constants_strategy61_correctness : sm2_constants_strategy61.
  Axiom sm2_constants_strategy71_correctness : sm2_constants_strategy71.
  Axiom sm2_constants_strategy81_correctness : sm2_constants_strategy81.
  Axiom sm2_constants_strategy83_correctness : sm2_constants_strategy83.
  Axiom sm2_constants_strategy85_correctness : sm2_constants_strategy85.
  Axiom sm2_constants_strategy87_correctness : sm2_constants_strategy87.
  Axiom sm2_constants_strategy89_correctness : sm2_constants_strategy89.
  Axiom sm2_constants_strategy91_correctness : sm2_constants_strategy91.

End sm2_constants_Strategy_Correct.
