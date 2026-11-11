From Coq Require Import ZArith.
Local Open Scope Z_scope.

(* rat_zero exposes the exact constants 0 and 1 directly.
   Existing simplex_rat_reduce_zero already supplies the rational-zero
   normalization theorem; no duplicate result predicate or lemma is needed. *)
