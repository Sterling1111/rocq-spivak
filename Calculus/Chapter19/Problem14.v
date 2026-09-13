From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_14 : ∀ F,
  (⟦ der ⟧ F = (λ x, exp x * sin x)) <->
  ∃ c, ∀ x, F x = exp x * (sin x - cos x)/2 + c.
Abort.
