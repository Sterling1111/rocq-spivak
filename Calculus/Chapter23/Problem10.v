From Calculus.Chapter23 Require Import Prelude.


Definition cauchy_product (a b : sequence) (n : nat) : R :=
  ∑ 1 n (λ k, a k * b (n + 1 - k)%nat).

Lemma problem_23_10 :
  let a := λ (n : ℕ), (-1)^n / √ (n : ℝ) in
  let c := cauchy_product a a in
  (∀ n, (n > 0)%nat -> |c n| >= 1) /\
  ~ ∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else c n) = S.
Abort.
