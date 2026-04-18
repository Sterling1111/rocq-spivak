From Calculus.Chapter19 Require Import Prelude.

(* Problem 6: A systematic selection of rational functions to be integrated. *)

Lemma lemma_19_6_i : forall c,
  ∫ (λ x, 1 / (x^2 - 1)) (-1, 1)^c = (λ x, log (Rabs ((x - 1) / (x + 1))) / 2 + c).
Abort.

Lemma lemma_19_6_ii : forall c,
  ∫ (λ x, 1 / (x^2 + 2*x + 1)) = (λ x, -1 / (x + 1) + c).
Abort.

Lemma lemma_19_6_iii : forall c,
  ∫ (λ x, x / (x^2 + 1)) = (λ x, log (x^2 + 1) / 2 + c).
Abort.

Lemma lemma_19_6_iv : forall c,
  ∫ (λ x, 1 / (x^2 + 1)^2) = (λ x, x / (2 * (x^2 + 1)) + arctan x / 2 + c).
Abort.
