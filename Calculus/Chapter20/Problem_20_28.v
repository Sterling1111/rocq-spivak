From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_28 : forall f a n,
  equal_up_to_order n f (P(n, a, f)) a.
Admitted.
