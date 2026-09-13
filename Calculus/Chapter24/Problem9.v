From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_9 : ∃ f,
  uniform_limit (λ N x, ∑ 1 N (λ (n : ℕ), x / (n * (1 + n * x^2)))) f (Full_set R).
Abort.
