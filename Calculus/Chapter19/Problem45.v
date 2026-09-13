From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_45_a : ∀ x, 0 < x ->
  improper_positive_19 (λ u, exp (-(u ^^ (1/x)))) (x*gamma_19 x).
Abort.

Lemma lemma_19_45_b : gamma_19 (1/2) = √π.
Abort.
