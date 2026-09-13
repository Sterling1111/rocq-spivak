From Calculus.Chapter20 Require Import Prelude.

Fixpoint real_binomial (α : ℝ) (n : ℕ) : ℝ :=
  match n with
  | O => 1
  | S k => real_binomial α k * (α-k) / (S k)
  end.

Lemma lemma_20_21_polynomial : ∀ α n x,
  P(n,0,λ y, (1+y) ^^ α) x = ∑ 0 n (λ k, real_binomial α k * x^k).
Abort.

Lemma lemma_20_21_cauchy : ∀ α n x, x > -1 -> x <> 0 ->
  ∃ t, Rmin 0 x < t < Rmax 0 x /\
    R(n,0,λ y, (1+y) ^^ α) x =
      (S n) * real_binomial α (S n) * x * (x-t)^n * (1+t) ^^ (α-n-1) /\
    R(n,0,λ y, (1+y) ^^ α) x =
      (S n) * real_binomial α (S n) * x * (1+t) ^^ (α-1) * ((x-t)/(1+t))^n.
Abort.

Lemma lemma_20_21_lagrange : ∀ α n x, x > -1 -> x <> 0 ->
  ∃ t, Rmin 0 x < t < Rmax 0 x /\
    R(n,0,λ y, (1+y) ^^ α) x = real_binomial α (S n) * x^(S n) * (1+t) ^^ (α-n-1).
Abort.
