From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_3_a : ∀ (p : nat) ε,
  ε > 0 -> ∃ N : nat, ∀ n : nat, (N <= n)%nat -> (0 < n)%nat ->
  |(∑ 1 n (λ (k : ℕ), k ^ p / n ^ (p + 1))) - 1 / (p + 1)%nat| < ε.
Abort.

Lemma lemma_13_3_b : ∀ (p : nat) b,
  b > 0 ->
  ∫ 0 b (λ x, x^p) = b^(p+1) / (p+1)%nat.
Abort.
