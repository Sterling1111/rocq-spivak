From Calculus.Chapter10 Require Import Prelude.

Definition Schwarzian_derivative (f : R -> R) (x : R) : R :=
  ⟦ Der ^ 3 x ⟧ f / ⟦ Der x ⟧ f - 3 / 2 * (⟦ Der ^ 2 x ⟧ f / ⟦ Der x ⟧ f)^2.

Notation "'D'" := Schwarzian_derivative.

Lemma lemma_10_19_a : ∀ f g x,
  nth_differentiable_at 3 g x ->
  nth_differentiable_at 3 f (g x) ->
  ⟦ Der x ⟧ g <> 0 ->
  ⟦ Der (g x) ⟧ f <> 0 ->
  D (f ∘ g) x = D f (g x) * (⟦ Der x ⟧ g)^2 + D g x.
Proof.
Abort.

Lemma lemma_10_19_b : ∀ a b c d,
  a * d - b * c ≠ 0 ->
  ∀ x, c * x + d ≠ 0 ->
  D (λ x, (a * x + b) / (c * x + d)) x = 0.
Proof. Abort.
