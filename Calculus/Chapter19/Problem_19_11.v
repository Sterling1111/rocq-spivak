From Calculus.Chapter19 Require Import Prelude.

(* Problem 11: Hyperbolic substitutions for integrals involving √(x^2-1) and √(x^2+1). *)

Lemma lemma_19_11_i : forall c,
  ∫ (λ x, √(x^2 - 1)) (1, ∞) =
    (λ x, x * √(x^2 - 1) / 2 - log (x + √(x^2 - 1)) / 2 + c).
Admitted.

Lemma lemma_19_11_ii : forall c,
  ∫ (λ x, 1 / √(x^2 - 1)) (1, ∞) =
    (λ x, log (x + √(x^2 - 1)) + c).
Admitted.
