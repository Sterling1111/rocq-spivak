From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_13_a : ∀ f n,
  (n > 1)%nat ->
  increasing_on f (λ x, 1 <= x) ->
  (∑ 1 (n - 1) (λ k, f k)) < (∫ 1 n f) /\ (∫ 1 n f) < (∑ 2 n (λ k, f k)).
Abort.

Lemma lemma_22_13_b : ∀ n,
  (n > 1)%nat ->
  n ^ n / exp ((n - 1)%nat) < n! < (n + 1)%nat ^ (n + 1) / exp n /\
  ⟦ lim ⟧ (λ n, n! ^^ (1 / n) / n) = 1 / exp 1.
Abort.
