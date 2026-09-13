From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_7 : ∀ (n : nat) c, (2 < n)%nat ->
  ∫ (λ x, 1 / √(x^n - x^2)) (1, ∞) =
    (λ x, 2 / (n - 2) * arctan (√(x^(n-2) - 1)) + c).
Abort.

Lemma lemma_19_7_arcsin : ∀ (n : nat) c, (2 < n)%nat ->
  ∫ (λ x, 1 / √(x^n - x^2)) (1, ∞) =
    (λ x, -2 / (n - 2) * arcsin (x ^^ (1 - n/2)) + c).
Abort.
