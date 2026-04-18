From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_22 : forall n f a x,
  R(n, a, f) x = f x - P(n, a, f) x.
Abort.
