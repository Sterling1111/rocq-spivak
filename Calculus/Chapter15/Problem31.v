From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_31_a :
  ~ ∃ (p q : R -> R),
    (∃ n, ∀ x, p x = sum_f 0 n (λ i, nth i nil 0 * x ^ i)) /\
    (∃ n, ∀ x, q x = sum_f 0 n (λ i, nth i nil 0 * x ^ i)) /\
    (∀ x, q x <> 0 -> sin x = p x / q x).
Abort.

Lemma lemma_15_31_b : ∀ (n : nat),
  ~ ∃ (fs : nat -> R -> R),
    (∀ i, ∃ (ci : list R), ∀ x, fs i x = sum_f 0 (length ci) (λ j, nth j ci 0 * x ^ j)) /\
    (∀ x, (sin x) ^ (S n) + ∑ 0 n (λ i, fs i x * (sin x) ^ i) = 0).
Abort.
