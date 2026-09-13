From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_1 : ∀ b,
  b > 0 ->
  ∫ 0 b (λ x, x^3) = b^4 / 4.
Abort.
