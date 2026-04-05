From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_35 : forall f,
  differentiable f -> (forall x y, f (x + y) = f x * f y) -> f 0 = 1 \/ f 0 = 0.
Admitted.
