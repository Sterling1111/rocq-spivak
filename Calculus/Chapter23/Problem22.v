From Calculus.Chapter23 Require Import Prelude.


Lemma problem_23_22_a : ∀ a b,
  bounded (λ n, ∑ 1 n a) ->
  nonincreasing (λ n, b (S n)) ->
  ⟦ lim ⟧ b = 0 ->
  ∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n * b n) = S.
Abort.

Lemma problem_23_22_b : ∀ b,
  nonincreasing (λ n, b (S n)) ->
  ⟦ lim ⟧ b = 0 ->
  ∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else (-1)^(n+1) * b n) = S.
Abort.

Lemma problem_23_22_c : ∀ x,
  (∀ k : Z, x <> 2 * k * π) ->
  ∃ S, ∑ 0 ∞ (λ (n : ℕ), if (n =? 0)%nat then 0 else cos (n * x) / n) = S.
Abort.

Lemma problem_23_22_c_divergence : ∀ k : Z,
  ~ series_converges (λ n, cos ((S n)%nat * (2 * k * π)) / (S n)%nat).
Abort.

Lemma problem_23_22_d : ∀ a b,
  (∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n) = S) ->
  (nondecreasing (λ n, b (S n)) \/ nonincreasing (λ n, b (S n))) ->
  bounded b ->
  ∃ S, ∑ 0 ∞ (λ n, if (n =? 0)%nat then 0 else a n * b n) = S.
Abort.
