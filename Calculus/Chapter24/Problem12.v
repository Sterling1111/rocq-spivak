From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_12_a : ∀ ε, 0 < ε -> ε < π -> ∃ f,
  uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), sin (n * x) / n)) f (λ x, ε <= x <= 2 * π - ε).
Abort.

Lemma lemma_24_12_b : ∀ f,
  ~ uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), sin (n * x) / n)) f (λ x, 0 <= x <= 2 * π).
Abort.
