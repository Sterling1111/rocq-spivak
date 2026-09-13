From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_17 : ∀ a b c x,
  (∀ n, c n = ∑ 0 n (λ k, a k * b (n - k))) ->
  series_converges (λ n, a n * x^n) ->
  series_converges (λ n, b n * x^n) ->
  series_converges (λ n, c n * x^n) /\
  ∀ A B, ∑ 0 ∞ (λ n, a n * x^n) = A -> ∑ 0 ∞ (λ n, b n * x^n) = B -> ∑ 0 ∞ (λ n, c n * x^n) = (A * B).
Abort.
