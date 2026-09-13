From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_26_a : ∀ fn f a b,
  (∀ n, integrable_on a b (fn n)) ->
  uniform_limit fn f (λ x, a <= x <= b) ->
  integrable_on a b f.
Abort.

Lemma lemma_24_26_d : ∃ f,
  uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), (-1)^n / (x + n))) f (λ x, x >= 0).
Abort.
