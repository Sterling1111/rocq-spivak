From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_6 : forall a b,
  0 < a 0%nat -> a 0%nat < b 0%nat ->
  (forall n, a (S n) = sqrt (a n * b n)) ->
  (forall n, b (S n) = (a n + b n) / 2) ->
  convergent_sequence a /\ convergent_sequence b /\
  (exists L, ⟦ lim ⟧ a = L /\ ⟦ lim ⟧ b = L).
Admitted.
