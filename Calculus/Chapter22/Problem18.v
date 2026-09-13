From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_18 : ∀ a L,
  (∀ n, a n > 0) ->
  ⟦ lim ⟧ (λ n, a (n + 1)%nat / a n) = L ->
  ⟦ lim ⟧ (λ n, a n ^^ (1 / n)) = L.
Abort.
