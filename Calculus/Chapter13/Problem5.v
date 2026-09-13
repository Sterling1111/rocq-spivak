From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_5_i :
  ∫ (-1) 1 (λ x, x^3 * sqrt(1 - x^2)) = 0.
Abort.

Lemma lemma_13_5_ii :
  ∫ (-1) 1 (λ x, (x^5 + 3) * √(1 - x^2)) = 3 * PI / 2.
Abort.
