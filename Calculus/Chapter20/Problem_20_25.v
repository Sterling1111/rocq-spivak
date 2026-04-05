From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_25 : forall f a x,
  limit_at_point (fun h => P(2, a, f) (a + h) - f (a + h)) 0 0.
Admitted.
