From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_11_a : ∀ a : sequence,
  (∀ n, a n > 0) -> 
  (∀ n, a (S n) <= a n / 2) ->
  ∀ ε : ℝ, ε > 0 -> ∃ n : ℕ, a n < ε.
Proof. Admitted.
