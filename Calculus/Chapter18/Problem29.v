From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_29_a : ∀ x n, 0 <= x ->
  sum_f_R0 (λ i, x^i / (fact i)) n <= exp x.
Abort.

Lemma lemma_18_29_b : ∀ n : nat,
  ⟦ lim ∞ ⟧ (λ x, exp x / x^n) = ∞.
Abort.
