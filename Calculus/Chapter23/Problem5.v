From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_5_a : ∀ a,
  series_converges_absolutely (λ n, a (S n)) ->
  series_converges_absolutely (λ n, a (S n)^3).
Abort.

Lemma problem_23_5_b :
  ∃ a,
    series_converges (λ n, a (S n)) /\
    ~ series_converges_absolutely (λ n, a (S n)) /\
    ~ series_converges (λ n, a (S n)^3).
Abort.
