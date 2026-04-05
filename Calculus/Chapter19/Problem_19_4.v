From Calculus.Chapter19 Require Import Prelude.

(* Problem 4: The following integrations can all be done with trig substitutions. *)

Lemma lemma_19_4_i : forall c,
  ∫ (λ x, 1 / √(1 - x^2)) (-1, 1) = (λ x, arcsin x + c).
Admitted.

Lemma lemma_19_4_ii : forall c,
  ∫ (λ x, √(1 - x^2)) (-1, 1) = (λ x, x * √(1 - x^2) / 2 + arcsin x / 2 + c).
Admitted.

Lemma lemma_19_4_iii : forall c,
  ∫ (λ x, 1 / √(1 + x^2)) = (λ x, log (x + √(1 + x^2)) + c).
Admitted.

Lemma lemma_19_4_iv : forall c,
  ∫ (λ x, √(1 + x^2)) = (λ x, x * √(1 + x^2) / 2 + log (x + √(1 + x^2)) / 2 + c).
Admitted.
