From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_10_a : ∀ a, a > 0 -> ∃ f,
  uniform_limit (λ N x, ∑ 0 N (λ n, 2^n * sin (1 / (3^n * x)))) f (λ x, x >= a).
Abort.

Lemma lemma_24_10_b : ∀ f,
  ~ uniform_limit (λ N x, ∑ 0 N (λ n, 2^n * sin (1 / (3^n * x)))) f (λ x, x > 0).
Abort.
