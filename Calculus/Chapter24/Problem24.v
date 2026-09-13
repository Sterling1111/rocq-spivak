From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_24 : ∀ f f',
  ⟦ der ⟧ f = f' ->
  ∃ fn, (∀ n, continuous (fn n)) /\ pointwise_limit fn f' (Full_set R).
Abort.
