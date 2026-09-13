From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_8 : ∀ a total N,
  (N > 0)%nat ->
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  nonincreasing (λ n, a (S n)) ->
  ⟦ lim ⟧ a = 0 ->
  (∑ 0 ∞ (λ n, (-1)^n * a (S n)) = total) ->
  |total - ∑ 1 N (λ n, (-1)^(n+1) * a n)| <= a (S N).
Abort.
