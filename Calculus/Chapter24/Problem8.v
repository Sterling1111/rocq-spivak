From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_8 :
  ~ (∀ (fn : nat -> R -> R) (Mn : nat -> R) A f,
      (∀ n x, x ∈ A -> 0 <= fn n x <= Mn n) ->
      (∀ n (ε : R), ε > 0 -> ∃ x, x ∈ A /\ fn n x > Mn n - ε) ->
      uniform_limit (λ N x, ∑ 0 N (λ n, fn n x)) f A ->
      series_converges Mn).
Abort.
