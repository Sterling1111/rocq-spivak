From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_20 : forall n a f,
  equal_up_to_order n f (P(n, a, f)) a.
Abort.
