From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_19 : ∀ a f,
  series_converges a ->
  (∀ x, 0 <= x <= 1 -> ∑ 0 ∞ (λ n, a n * x^n) = (f x)) ->
  uniform_limit (λ N x, ∑ 0 N (λ n, a n * x^n)) f (λ x, 0 <= x <= 1).
Abort.
