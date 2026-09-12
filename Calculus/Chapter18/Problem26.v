From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_26 : ∀ f,
  (integrable_on 0 1 f /\
  ⟦ der ⟧ f = (λ t, f t + ∫ 0 1 f)) <->
  (∃ c, ∀ t, f t = c * (exp t - (e - 1) / 2)).
Abort.
