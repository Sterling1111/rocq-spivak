From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_14_even : ∀ a R_val,
  R_val > 0 ->
  (∀ x, Rabs x < R_val -> series_converges (λ n, a n * x^n)) ->
  (∀ x S, Rabs x < R_val -> (∑ 0 ∞ (λ n, a n * x^n) = S) -> (∑ 0 ∞ (λ n, a n * (-x)^n) = S)) ->
  ∀ n, Nat.Odd n -> a n = 0.
Abort.

Lemma lemma_24_14_odd : ∀ a R_val,
  R_val > 0 ->
  (∀ x, Rabs x < R_val -> series_converges (λ n, a n * x^n)) ->
  (∀ x S, Rabs x < R_val -> ∑ 0 ∞ (λ n, a n * x^n) = S -> ∑ 0 ∞ (λ n, a n * (-x)^n) = (- S)) ->
  ∀ n, Nat.Even n -> a n = 0.
Abort.
