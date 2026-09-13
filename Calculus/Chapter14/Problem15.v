From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_15_a : ∃ g : R -> R,
  (∀ x, x >= 0 ->
    ∫ (x^2) (2*x^2) (λ t, 1) * x =
    ∫ 0 x (λ t, 2*t^2 - g t)).
Abort.

Lemma lemma_14_15_b : ∀ (m : nat) (c : R),
  c > 1 ->
  ∃ g : R -> R,
  ∀ x, x >= 0 ->
    ∫ (x ^ m) (c * x ^ m) (λ t, 1) * x =
    ∫ 0 x (λ t, c * t ^ m - g t).
Abort.
