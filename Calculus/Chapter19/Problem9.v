From Calculus.Chapter19 Require Import Prelude.

(* Problem 9: Find the following integrals. *)

Lemma lemma_19_9_i : forall c,
  ∫ (λ x, x * log x) (0, ∞) = (λ x, x^2 / 2 * log x - x^2 / 4 + c).
Abort.

Lemma lemma_19_9_ii : forall c,
  ∫ (λ x, x^2 * exp x) = (λ x, (x^2 - 2*x + 2) * exp x + c).
Abort.

Lemma lemma_19_9_iii : forall c,
  ∫ (λ x, x * arctan x) = (λ x, (x^2 + 1) / 2 * arctan x - x / 2 + c).
Abort.
