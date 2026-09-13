From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_14_a : ∀ a b,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  rearrangement (λ n, b (S n)) (λ n, a (S n)) ->
  ∀ n, (n > 0)%nat -> ∃ m, (m > 0)%nat /\ ∑ 1 n a <= ∑ 1 m b.
Abort.

Lemma problem_23_14_b : ∀ a b total_b,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  rearrangement (λ n, b (S n)) (λ n, a (S n)) ->
  (∑ 0 ∞ (λ n, b (S n)) = total_b) ->
  ∃ total_a, (∑ 0 ∞ (λ n, a (S n)) = total_a) /\ total_a <= total_b.
Abort.

Lemma problem_23_14_c : ∀ a b total,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  rearrangement (λ n, b (S n)) (λ n, a (S n)) ->
  ((∑ 0 ∞ (λ n, a (S n)) = total) <->
   (∑ 0 ∞ (λ n, b (S n)) = total)).
Abort.

Lemma problem_23_14_d : ∀ a b total,
  series_converges_absolutely (λ n, a (S n)) ->
  rearrangement (λ n, b (S n)) (λ n, a (S n)) ->
  (∑ 0 ∞ (λ n, a (S n)) = total) ->
  series_converges_absolutely (λ n, b (S n)) /\
  (∑ 0 ∞ (λ n, b (S n)) = total).
Abort.
