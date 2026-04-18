From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_14_a : ∀ a b : sequence,
  (∀ n, a n <= a (S n)) ->
  (∀ n, b (S n) <= b n) ->
  (∀ n, a n <= b n) ->
  ∃ x, ∀ n, a n <= x <= b n.
Proof. Abort.

Lemma lemma_8_14_b :
  ∃ a b : sequence,
    (∀ n, a n <= a (S n)) /\
    (∀ n, b (S n) <= b n) /\
    (∀ n, a n < b n) /\
    ~ (∃ x, ∀ n, a n < x < b n).
Proof. Abort.
