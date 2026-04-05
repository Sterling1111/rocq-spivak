From Calculus.Chapter15 Require Import Prelude.

(* Problem 16: Find sin(arctan x) and cos(arctan x) *)

Lemma lemma_15_16_sin : forall x,
  sin (arctan x) = x / √(1 + x^2).
Admitted.

Lemma lemma_15_16_cos : forall x,
  cos (arctan x) = 1 / √(1 + x^2).
Admitted.
