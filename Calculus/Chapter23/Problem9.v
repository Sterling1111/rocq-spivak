From Calculus.Chapter23 Require Import Prelude.
From Calculus.Chapter22 Require Import Problem27.

Lemma problem_23_9_a : ∀ a r,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  ⟦ lim ⟧ (λ n, a (S n) ^^ (1 / (S n)%nat)) = r ->
  (r < 1 -> series_converges (λ n, a (S n))) /\
  (r > 1 -> ~ series_converges (λ n, a (S n))).
Abort.

Lemma problem_23_9_a_delicate : ∀ a,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  ((∃ s N, s < 1 /\ ∀ (n : ℕ), (n >= N)%nat -> (n > 0)%nat ->
      a n ^^ (1 / n) <= s) -> series_converges (λ n, a (S n))) /\
  ((∀ N, ∃ (n : ℕ), (n >= N)%nat /\ (n > 0)%nat /\
      a n ^^ (1 / n) >= 1) -> ~ series_converges (λ n, a (S n))).
Abort.

Lemma problem_23_9_a_limsup : ∀ a r,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  sequence_limsup (λ n, a (S n) ^^ (1 / (S n)%nat)) r ->
  (r < 1 -> series_converges (λ n, a (S n))) /\
  (r > 1 -> ~ series_converges (λ n, a (S n))).
Abort.

Lemma problem_23_9_a_inconclusive :
  ∃ a b,
    (∀ n, a n >= 0 /\ b n >= 0) /\
    ⟦ lim ⟧ (λ n, a (S n) ^^ (1 / (S n)%nat)) = 1 /\
    ⟦ lim ⟧ (λ n, b (S n) ^^ (1 / (S n)%nat)) = 1 /\
    series_converges (λ n, a (S n)) /\
    ~ series_converges (λ n, b (S n)).
Abort.

Lemma problem_23_9_b : ∀ a r,
  (∀ n, (n > 0)%nat -> a n > 0) ->
  ⟦ lim ⟧ (λ n, a (S n) / a n) = r ->
  ⟦ lim ⟧ (λ n, a (S n) ^^ (1 / (S n)%nat)) = r.
Abort.
