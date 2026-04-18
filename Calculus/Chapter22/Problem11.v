From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_11_a : forall a L,
  ⟦ lim ⟧ a = L -> bounded a.
Abort.

Lemma lemma_22_11_b : forall a,
  ⟦ lim ⟧ a = 0 -> (exists n, a n > 0) ->
  exists n, forall m, a m <= a n.
Abort.
