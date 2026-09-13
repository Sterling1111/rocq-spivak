From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_28_b : ∀ fn f a b,
  (∀ n, continuous_on (fn n) (λ x, a <= x <= b)) ->
  continuous_on f (λ x, a <= x <= b) ->
  (∀ n x, a <= x <= b -> fn (S n) x <= fn n x) ->
  pointwise_limit fn f (λ x, a <= x <= b) ->
  uniform_limit fn f (λ x, a <= x <= b).
Abort.
