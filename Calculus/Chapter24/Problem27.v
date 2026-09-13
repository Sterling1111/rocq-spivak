From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_27 : ∀ fn f,
  (∀ n, continuous_on (fn n) (λ x, 0 <= x <= 1)) ->
  uniform_limit fn f (λ x, 0 <= x <= 1) ->
  ⟦ lim ⟧ (λ (n : ℕ), ∫ 0 (1 - 1 / n) (fn n)) = ∫ 0 1 f.
Abort.
