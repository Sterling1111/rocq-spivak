From Calculus.Chapter19 Require Import Prelude.

(* Problem 5: The following integrations involve substitutions of various types. *)

Lemma lemma_19_5_i : forall c,
  ∫ (λ x, x / (1 + x^2)) = (λ x, log (1 + x^2) / 2 + c).
Admitted.

Lemma lemma_19_5_ii : forall c,
  ∫ (λ x, x^2 / (1 + x^3)) (0, ∞) = (λ x, log (1 + x^3) / 3 + c).
Admitted.

Lemma lemma_19_5_iii : forall c,
  ∫ (λ x, exp x / (1 + exp x)) = (λ x, log (1 + exp x) + c).
Admitted.
