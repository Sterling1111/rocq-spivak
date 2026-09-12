From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_15_a : ∀ (n : ℕ), (0 < n) ->
  (∀ x, x > 0 -> exp x / x^n >= exp n / n^n) /\
  (∀ x, x > n -> exp x / x^n > exp n / n^n).
Proof.
Abort.

Lemma lemma_18_15_b : ∀ (n : nat), (0 < n)%nat ->
  (⟦ der ⟧ (λ x, exp x / x^n) (0, ∞) =
    (λ x, exp x * (x - n) / x^(S n))) /\
  (∀ x, x > (S n) ->
    exp x * (x - n) / x^(S n) > exp (S n) / (S n)^(S n)) /\
  ⟦ lim ∞ ⟧ (λ x, exp x / x^n) = ∞.
Abort.
