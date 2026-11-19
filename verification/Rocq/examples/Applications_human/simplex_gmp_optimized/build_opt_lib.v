From Coq Require Import ZArith Lia String.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.simplex_gmp_minimal
  Require Export build_fme_model_input_revision_lib.
From SimpleC.EE.Applications_human.simplex_gmp_minimal
  Require Import integers_fme_model_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

(* Logical dimensions for the Arch32 model: m input rows and n original
   variables. The square table block and the full index array bound every
   other allocated span. Array ownership and the configured mpz field
   layout are separate facts. *)
Definition simplex_dimensions_ok (m n : Z) : Prop :=
  0 <= m /\ 0 <= n /\ m + n < UINT_MAX /\
  m * (m + n) * 12 <= INT_MAX /\
  (m + n) * 4 <= INT_MAX.

(* Both the original and compacted table fit when rows are discarded. *)
Lemma simplex_dimensions_smaller m n kept :
  simplex_dimensions_ok m n -> 0 <= kept <= m ->
  simplex_dimensions_ok kept n.
Proof.
  unfold simplex_dimensions_ok.
  intros (Hm & Hn & Hsum & Hmul & Hindices) Hkept.
  assert (Hmonotone : kept * (kept + n) <= m * (m + n)).
  { apply Z.mul_le_mono_nonneg; lia. }
  repeat split; try lia.
Qed.

(* The projected byte/count bounds justify allocation and index arithmetic.
   An optimized temporary node contains exactly two Arch32 pointers. *)
Lemma simplex_dimensions_bounds m n :
  simplex_dimensions_ok m n ->
  0 <= m * (m + n) <= INT_MAX /\
  0 <= 12 * m <= INT_MAX /\
  0 <= 4 * m <= INT_MAX /\
  0 <= 4 * n <= INT_MAX /\
  0 <= 8 * m <= INT_MAX /\
  0 <= n <= INT_MAX /\
  n + 1 <= UINT_MAX.
Proof.
  unfold simplex_dimensions_ok.
  intros (Hm & Hn & Hsum & Hmul & Hindices).
  assert (Hprod : 0 <= m * (m+n)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hmprod : m <= m * (m+n)).
  { destruct (Z.eq_dec m 0) as [->|Hpositive].
    - lia.
    - replace m with (m * 1) at 1 by lia.
      apply Z.mul_le_mono_nonneg_l; lia. }
  repeat split; lia.
Qed.

(* Convert the mathematical byte bound to the symbolic C typedef size.
   When m=0 there is no mpz array element to inspect. *)
Lemma simplex_dimensions_mpz_bytes m n :
  simplex_dimensions_ok m n ->
  (0 < m -> simplex_mpz_layout) ->
  0 <= m * sizeof("__mpz_struct") <= INT_MAX /\
  0 <= m * (m + n) * sizeof("__mpz_struct") <= INT_MAX /\
  (0 < m -> (n + 1) * sizeof("__mpz_struct") <= INT_MAX).
Proof.
  intros Hdim Hlayout.
  pose proof (simplex_dimensions_bounds _ _ Hdim) as Hbounds.
  unfold simplex_dimensions_ok in Hdim.
  destruct Hdim as (Hm & Hn & Hsum & Hmul & Hindices).
  destruct (Z.eq_dec m 0) as [->|Hpositive].
  - repeat split; lia.
  - destruct (Hlayout ltac:(lia)) as [Hsize _].
    assert (Hrows : m + n <= m * (m + n)).
    { replace (m + n) with (1 * (m+n)) at 1 by lia.
      apply Z.mul_le_mono_nonneg_r; lia. }
    rewrite Hsize. repeat split; lia.
Qed.

(* Row-major offsets for an existing row and column. *)
Lemma simplex_dimensions_index m n r v :
  simplex_dimensions_ok m n ->
  0 <= r < m -> 0 <= v < m+n ->
  0 <= r * (m+n) + v < m * (m+n).
Proof.
  intros Hdim Hr Hv.
  assert (Hrow : (r+1) * (m+n) <= m * (m+n)).
  { apply Z.mul_le_mono_nonneg_r; lia. }
  split.
  - assert (Hprod : 0 <= r * (m+n)) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - nia.
Qed.

(* QCP gives a by-value result a synthetic uninitialised output slot.
   This is the actual eight-field layout including nonbasic. *)
Definition UndefStructPredtable (p : Z) : Assertion :=
  &(p # "table" ->ₛ "rows") # UInt |->_ **
  &(p # "table" ->ₛ "cols") # UInt |->_ **
  &(p # "table" ->ₛ "d") # Ptr |->_ **
  &(p # "table" ->ₛ "c") # Ptr |->_ **
  &(p # "table" ->ₛ "a") # Ptr |->_ **
  &(p # "table" ->ₛ "basic") # Ptr |->_ **
  &(p # "table" ->ₛ "row") # Ptr |->_ **
  &(p # "table" ->ₛ "nonbasic") # Ptr |->_.
