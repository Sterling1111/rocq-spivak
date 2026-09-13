From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_23 : ∀ T M k,
  k > 0 -> ⟦ der ⟧ T = (λ t, - k * (T t - M)) ->
  ∀ t, T t = M + (T 0 - M) * exp (- k * t).
Abort.
