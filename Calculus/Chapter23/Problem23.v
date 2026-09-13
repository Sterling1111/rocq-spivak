From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_23 : ∀ a,
  decreasing (λ n, a (S n)) ->
  ⟦ lim ⟧ a = 0 ->
  series_converges (λ n, a (S n)) ->
  series_converges (λ n, 2^(S n) * a (2^(S n))%nat).
Abort.
