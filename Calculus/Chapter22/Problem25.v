From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_25 : ∀ b f L,
  (∀ n, b (S n) = f (b n)) ->
  ⟦ lim ⟧ b = L ->
  (∀ n, b n <> L) ->
  (∃ δ, δ > 0 /\ differentiable_on f (L - δ, L + δ)) ->
  continuous_at (⟦ Der ⟧ f) L ->
  |(⟦ Der ⟧ f) L| <= 1.
Abort.
