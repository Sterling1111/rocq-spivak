From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_19_a : forall a L,
  (forall n, 0 <= a n <= 1) ->
  ⟦ lim ⟧ a = L ->
  0 <= L <= 1.
Admitted.

Lemma lemma_22_19_b : exists a L,
  (forall n, 0 < a n < 1) /\ ⟦ lim ⟧ a = L /\ ~ (0 < L < 1).
Admitted.
