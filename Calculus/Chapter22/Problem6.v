From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_6 : ∀ a b,
  0 < a 0%nat -> a 0%nat < b 0%nat ->
  (∀ n, a (S n) = √ (a n * b n)) ->
  (∀ n, b (S n) = (a n + b n) / 2) ->
  convergent_sequence a /\ convergent_sequence b /\
  (∃ L, ⟦ lim ⟧ a = L /\ ⟦ lim ⟧ b = L).
Abort.
