From Calculus.Chapter23 Require Import Prelude.


Lemma problem_23_16 : ∀ a S_abs S_total,
  series_converges_absolutely (λ n, a (S n)) ->
  (∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n) = S_total) ->
  (∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else |a n|) = S_abs) ->
  |S_total| <= S_abs.
Abort.
