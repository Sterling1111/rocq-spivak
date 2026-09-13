From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_44 : improper_positive_19 (λ x, sin x/x) (π/2) ->
  improper_positive_19 (λ x, (sin x/x)^2) (π/2).
Abort.
