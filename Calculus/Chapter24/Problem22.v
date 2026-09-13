From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_22 : ∀ a, 0 < a < 1 ->
  uniform_limit (λ N x, ∑ 0 N (λ n, x^(2*n+1) / (2*n+1)%nat - x^(n+1) / (2*n+2)%nat))
                (λ x, 1 / 2 * ln (x + 1))
                (λ x, -a <= x <= a) /\ ∑ 0 ∞ (λ n, 1^n / (2*n+1)%nat - 1^n / (2*n+2)%nat) = (ln 2).
Abort.
