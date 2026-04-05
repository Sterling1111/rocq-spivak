From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_4_a : forall a b L,
  cauchy_sequence a ->
  subsequence b a ->
  ⟦ lim ⟧ b = L ->
  ⟦ lim ⟧ a = L.
Admitted.

Lemma lemma_22_4_b : forall a b L,
  ⟦ lim ⟧ a = L ->
  subsequence b a ->
  ⟦ lim ⟧ b = L.
Admitted.
