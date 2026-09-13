From Calculus.Chapter24 Require Import Prelude.

Fixpoint choose_R (alpha : R) (n : nat) : R :=
  match n with
  | 0%nat => 1
  | S n' => choose_R alpha n' * (alpha - n') / (S n')%nat
  end.

Lemma lemma_24_7_a : ∀ α x f,
  (∀ y, Rabs y < 1 -> ∑ 0 ∞ (λ n, choose_R α n * y ^ n) = (f y)) ->
  Rabs x < 1 ->
  (1 + x) * ⟦ Der x ⟧ f = α * f x.
Abort.

Lemma lemma_24_7_b : ∀ α f,
  (∀ x, Rabs x < 1 -> (1 + x) * ⟦ Der x ⟧ f = α * f x) ->
  ∃ c, ∀ x, Rabs x < 1 -> f x = c * Rpower (1 + x) α.
Abort.
