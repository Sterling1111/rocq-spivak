From Calculus.Chapter15 Require Import Prelude.

(* Problem 25: |sin x - sin y| < |x - y| for all x ≠ y *)
Lemma lemma_15_25 : forall x y,
  x <> y ->
  |sin x - sin y| < |x - y|.
Admitted.
