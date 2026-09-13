From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_8_a : ∀ a,
  a > 0 ->
  ∫ (-a) a (λ x, 4 * (a^2 - x^2)) = 16 / 3 * a^3.
Abort.

Lemma lemma_19_App_8_b : ∀ a, 0 < a ->
  ∫ (-a) a (λ x, √3*(a^2-x^2)) = 4*√3*a^3/3.
Abort.
