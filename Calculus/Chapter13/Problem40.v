From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_40 : ∀ f L,
  (∀ x, x > 0 -> integrable_on 0 x f) ->
  ⟦ lim ∞ ⟧ f = L ->
  ⟦ lim ∞ ⟧ (λ x, (1 / x) * ∫ 0 x f) = L.
Abort.
