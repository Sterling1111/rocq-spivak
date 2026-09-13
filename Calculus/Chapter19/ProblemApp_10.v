From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_10 : ∀ r,
  r > 0 ->
  ∫ (-r) r (λ x, 4 * (r^2 - x^2)) = 16 / 3 * r^3.
Abort.
