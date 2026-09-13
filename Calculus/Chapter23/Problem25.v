From Calculus.Chapter23 Require Import Prelude.


Lemma problem_23_25 : ∀ a,
  (∀ n, (n > 0)%nat -> a n > 0) ->
  decreasing (λ n, a (S n)) ->
  (∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n) = S) ->
  ⟦ lim ⟧ (λ (n : ℕ), n * a n) = 0.
Abort.
