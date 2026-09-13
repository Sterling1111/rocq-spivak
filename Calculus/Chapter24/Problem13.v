From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_13_a : ∀ a R,
  R > 0 ->
  (∀ x, Rabs x < R -> series_converges (λ n, a n * x^n) /\ ∑ 0 ∞ (λ n, a n * x^n) = 0) ->
  ∀ n, a n = 0.
Abort.

Lemma lemma_24_13_b : ∀ a (x : nat -> R),
  (∀ n, x n <> 0) ->
  ⟦ lim ⟧ x = 0 ->
  (∀ n, series_converges (λ k, a k * (x n)^k) /\ ∑ 0 ∞ (λ k, a k * (x n)^k) = 0) ->
  ∀ n, a n = 0.
Abort.

Lemma lemma_24_13_c : ∀ a b (x : nat -> R),
  (∀ n, x n <> 0) ->
  ⟦ lim ⟧ x = 0 ->
  (∀ n, series_converges (λ k, a k * (x n)^k) /\ series_converges (λ k, b k * (x n)^k) /\
             ∃ L, ∑ 0 ∞ (λ k, a k * (x n)^k) = L /\ ∑ 0 ∞ (λ k, b k * (x n)^k) = L) ->
  ∀ n, a n = b n.
Abort.
