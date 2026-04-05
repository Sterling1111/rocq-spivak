From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_25 : forall f,
  differentiable f -> ⟦ der ⟧ f = f -> f 0 = 1 -> f = exp.
Admitted.
