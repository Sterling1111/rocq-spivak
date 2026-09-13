From Calculus.Chapter23 Require Import Prelude.
Require Import Calculus.Chapter23.Problem12.


Lemma problem_23_13 : ∀ a l,
  (∀ n, (n > 0)%nat -> a n > 0) ->
  cesaro_summable a l ->
  bounded (λ (n : ℕ), n * a n) ->
  ∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n) = S.
Abort.
