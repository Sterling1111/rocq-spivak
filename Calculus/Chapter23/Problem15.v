From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_15_a : ∀ a b,
  series_converges_absolutely (λ n, a (S n)) ->
  subsequence (λ n, b (S n)) (λ n, a (S n)) ->
  series_converges_absolutely (λ n, b (S n)).
Abort.

Lemma problem_23_15_b :
  ∃ a b,
    series_converges (λ n, a (S n)) /\
    ~ series_converges_absolutely (λ n, a (S n)) /\
    subsequence (λ n, b (S n)) (λ n, a (S n)) /\
    ~ series_converges (λ n, b (S n)).
Abort.

Lemma problem_23_15_c : ∀ a,
  series_converges_absolutely (λ n, a (S n)) ->
  ∃ total odd even,
    (∑ 0 ∞ (λ n, a (S n)) = total) /\
    (∑ 0 ∞ (λ n, a (2*n+1)%nat) = odd) /\
    (∑ 0 ∞ (λ n, a (2*n+2)%nat) = even) /\ total = odd + even.
Abort.
