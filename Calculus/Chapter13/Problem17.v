From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_17 : ∀ a b,
  0 < a -> 0 < b ->
  ∫ (-1) 1 (λ x, 2 * √(1 - x^2)) = PI ->
  ∫ (-a) a (λ x, 2 * b * √(1 - x^2 / a^2)) = PI * a * b.
Abort.
