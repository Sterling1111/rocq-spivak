From Calculus.Chapter23 Require Import Prelude.

Fixpoint generalized_choose (α : R) (k : nat) : R :=
  match k with
  | O => 1
  | S j => (α - j) / (S j)%nat * generalized_choose α j
  end.

Lemma problem_23_21_a : ∀ α r, |r| < 1 ->
  series_converges (λ k, generalized_choose α k * r^k) /\
  ⟦ lim ⟧ (λ n, generalized_choose α n * r^n) = 0.
Abort.

Lemma problem_23_21_b_bound : ∀ α x t (n : ℕ),
  0 <= x < 1 -> 0 <= t <= x -> (S n)%nat > α ->
  (1+t) ^^ (α - n - 1) <= 1.
Abort.

Lemma problem_23_21_b : ∀ α x, 0 <= x < 1 ->
  ⟦ lim ⟧ (λ n, R(n, 0, (λ y, (1+y) ^^ α)) x) = 0.
Abort.

Lemma problem_23_21_c_bounds : ∀ α x t,
  -1 < x < 0 -> x < t <= 0 ->
  |x * (1+t) ^^ (α-1)| <= |x| * Rmax 1 ((1+x) ^^ (α-1)) /\
  |(x-t)/(1+t)| = |x| * ((1-t/x)/(1+t)) /\
  |(x-t)/(1+t)| <= |x|.
Abort.

Lemma problem_23_21_c_coefficients : ∀ α n,
  (S n)%nat * generalized_choose α (S n) = α * generalized_choose (α-1) n.
Abort.

Lemma problem_23_21_c : ∀ α x, -1 < x < 0 ->
  ⟦ lim ⟧ (λ n, R(n, 0, (λ y, (1+y) ^^ α)) x) = 0.
Abort.

Lemma problem_23_21 : ∀ α x, |x| < 1 ->
  ∑ 0 ∞ (λ k, generalized_choose α k * x^k) = ((1+x) ^^ α).
Abort.
