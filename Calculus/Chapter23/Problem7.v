From Calculus.Chapter23 Require Import Prelude.


Lemma problem_23_7_a : ∀ a,
  (∀ n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) ->
  (∀ n, (n > 0)%nat -> ∃ (k : nat), a n = (k : ℝ)) ->
  ∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n / 10^n) = S /\ 0 <= S /\ S <= 1.
Abort.

Lemma problem_23_7_b : ∀ x,
  0 <= x <= 1 ->
  ∃ a S,
    (∀ n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) /\
    (∀ n, (n > 0)%nat -> ∃ (k : nat), a n = (k : ℝ)) /\
    ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n / 10^n) = S /\ S = x.
Abort.

Definition eventually_repeating (a : sequence) : Prop :=
  ∃ N p, (p > 0)%nat /\ ∀ n, (n >= N)%nat -> a (n + p)%nat = a n.

Lemma problem_23_7_c : ∀ a x,
  (∀ n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) ->
  (∀ n, (n > 0)%nat -> ∃ (k : nat), a n = (k : ℝ)) ->
  eventually_repeating a ->
  ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n / 10^n) = x ->
  rational x.
Abort.

Lemma problem_23_7_c_value : ∀ a p,
  (p > 0)%nat ->
  (∀ n, (n > 0)%nat -> 0 <= a n <= 9) ->
  (∀ n, (n > 0)%nat -> ∃ k : nat, a n = (k : ℝ)) ->
  (∀ n, (n > 0)%nat -> a (n+p)%nat = a n) ->
  ∃ x, (∑ 0 ∞ (λ n, a (S n) / 10^(S n)) = x) /\
    x = (∑ 1 p (λ k, a k * 10^(p-k))) / (10^p - 1) /\ rational x.
Abort.

Lemma problem_23_7_d : ∀ a x,
  (∀ n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) ->
  (∀ n, (n > 0)%nat -> ∃ (k : nat), a n = (k : ℝ)) ->
  ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n / 10^n) = x ->
  rational x ->
  eventually_repeating a.
Abort.
