From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_24 : forall f f',
  ⟦ der ⟧ f = f' ->
  exists fn, (forall n, continuous (fn n)) /\ pointwise_limit fn f' (Full_set R).
Admitted.
