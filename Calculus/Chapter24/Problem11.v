From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_11_a : ∀ a, a > 0 -> ∃ f,
  uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), n * x / (1 + n ^ 4 * x ^ 2))) f (λ x, x >= a).
Abort.

Lemma lemma_24_11_b : ∀ f,
  ~ uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), n * x / (1 + n ^ 4 * x ^ 2))) f (Full_set R).
Abort.

Lemma lemma_24_11_c : ∃ f,
  uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), n * x / (1 + n ^ 5 * x ^ 2))) f (Full_set R).
Abort.
