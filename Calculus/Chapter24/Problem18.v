From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_18 : ∀ (a : nat -> R) x0,
  a 0%nat = 1 ->
  x0 <> 0 -> series_converges (λ n, a n * x0^n) ->
  ∃ (b : nat -> R),
    b 0%nat = 1 /\ (∀ n, (n > 0)%nat -> b n = - ∑ 0 (n - 1) (λ k, b k * a (n - k)%nat)) /\
    ∃ x1, x1 <> 0 /\ series_converges (λ n, b n * x1^n).
Abort.
