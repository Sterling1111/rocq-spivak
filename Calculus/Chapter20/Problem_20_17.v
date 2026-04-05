From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_17 : forall f a n,
  nth_differentiable_at n f a ->
  ⟦ Der ^ n a ⟧ f = 0 \/ ⟦ Der ^ n a ⟧ f <> 0.
Admitted.
