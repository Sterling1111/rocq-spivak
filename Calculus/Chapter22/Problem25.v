From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_25 : forall b f L,
  (forall n, b (S n) = f (b n)) ->
  ⟦ lim ⟧ b = L ->
  differentiable_at f L ->
  continuous_at (⟦ der ⟧ f) L ->
  Rabs (⟦ der ⟧ f L) <= 1.
Abort.
