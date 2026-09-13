From Calculus.Chapter23 Require Import Prelude.



Lemma problem_23_6_a : ∀ f a,
  (∃ δ, δ > 0 /\ continuous_on f (-δ, δ)) ->
  (∃ N, ∀ (n : ℕ), (n >= N)%nat -> (n > 0)%nat -> a n = f (1 / n)) ->
  (∃ total, ∑ 0 ∞ (λ n, a (S n)) = total) ->
  f 0 = 0.
Abort.

Lemma problem_23_6_b : ∀ f f' a,
  (∃ δ, δ > 0 /\ continuous_on f (-δ, δ)) ->
  ⟦ der 0 ⟧ f = f' ->
  (∃ N, ∀ (n : ℕ), (n >= N)%nat -> (n > 0)%nat -> a n = f (1 / n)) ->
  (∃ total, ∑ 0 ∞ (λ n, a (S n)) = total) ->
  f' 0 = 0.
Abort.

Lemma problem_23_6_c : ∀ f f' f'' a,
  (∃ δ, δ > 0 /\ continuous_on f (-δ, δ)) ->
  ⟦ der 0 ⟧ f = f' ->
  ⟦ der^2 0 ⟧ f = f'' ->
  f 0 = 0 ->
  f' 0 = 0 ->
  (∃ N, ∀ (n : ℕ), (n >= N)%nat -> (n > 0)%nat -> a n = f (1 / n)) ->
  ∃ total, ∑ 0 ∞ (λ n, a (S n)) = total.
Abort.

Lemma problem_23_6_d :
  ~ (∀ f a,
      (∃ δ, δ > 0 /\ continuous_on f (-δ, δ)) ->
      (∃ N, ∀ (n : ℕ), (n >= N)%nat -> (n > 0)%nat -> a n = f (1 / n)) ->
      (∃ total, ∑ 0 ∞ (λ n, a (S n)) = total) ->
      ∃ f', ⟦ der 0 ⟧ f = f').
Abort.

Lemma problem_23_6_e :
  ~ (∀ f f' a,
      (∃ δ, δ > 0 /\ continuous_on f (-δ, δ)) ->
      ⟦ der 0 ⟧ f = f' ->
      f 0 = 0 ->
      f' 0 = 0 ->
      (∃ N, ∀ (n : ℕ), (n >= N)%nat -> (n > 0)%nat -> a n = f (1 / n)) ->
      ∃ total, ∑ 0 ∞ (λ n, a (S n)) = total).
Abort.
