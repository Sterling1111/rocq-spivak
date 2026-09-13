From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_25 : ∃ fn f a b,
  (∀ n, integrable_on a b (fn n)) /\ (∀ x, rational x -> f x = 1) /\ (∀ x, irrational x -> f x = 0) /\ pointwise_limit fn f (λ x, a <= x <= b).
Abort.
