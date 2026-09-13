From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_23_a : ∀ fn f a b,
  (∀ n x, a <= x <= b -> ∃ M, Rabs (fn n x) <= M) ->
  uniform_limit fn f (λ x, a <= x <= b) ->
  ∃ M, ∀ x, a <= x <= b -> Rabs (f x) <= M.
Abort.

Lemma lemma_24_23_b : ∃ fn f a b,
  (∀ n, continuous_on (fn n) (λ x, a <= x <= b)) /\ pointwise_limit fn f (λ x, a <= x <= b) /\ ~ ∃ M, ∀ x, a <= x <= b -> Rabs (f x) <= M.
Abort.
