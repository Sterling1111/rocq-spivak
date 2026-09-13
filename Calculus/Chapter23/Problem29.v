From Calculus.Chapter23 Require Import Prelude.

From Calculus.Chapter23 Require Import Problem28.

Lemma problem_23_29_a :
  ⟦ lim ⟧ (λ N, prod_f 2 N (λ (n : ℕ), 1 - 1 / n^2)) = (1/2).
Abort.

Lemma problem_23_29_b : ∀ x, |x| < 1 ->
  ⟦ lim ⟧ (λ N, prod_f 1 N (λ n, 1 + x^(2^n)%nat)) = (1 / (1-x^2)).
Abort.
