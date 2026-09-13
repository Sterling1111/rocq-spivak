From Calculus.Chapter23 Require Import Prelude.


Lemma problem_23_24_a : ∀ a b,
  (∃ S1, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else (a n)^2) = S1) ->
  (∃ S2, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else (b n)^2) = S2) ->
  ∃ S3, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n * b n) = S3.
Abort.

Lemma problem_23_24_b : ∀ a α,
  (∃ S1, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else (a n)^2) = S1) ->
  α > 1 / 2 ->
  ∃ S2, ∑ 0 ∞ (λ (n : ℕ), if (n =? 0)%nat then 0 else a n / n ^^ α) = S2.
Abort.
