From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_1_a :
  π * ∫ 0 1 (λ x, x^2 - (x^2)^2) = 2 * π / 15.
Abort.

Lemma lemma_19_App_1_b : 2*π * ∫ 0 1 (λ x, x*(x-x^2)) = π/6.
Abort.
