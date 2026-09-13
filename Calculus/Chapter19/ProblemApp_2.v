From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_2 : ∀ r,
  r > 0 ->
  π * ∫ (-r) r (λ x, r^2 - x^2) = 4 / 3 * π * r^3.
Abort.
