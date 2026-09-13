From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_16_a : ∀ c,
  ∫ (λ x, arcsin x) (-1, 1) = (λ x, x * arcsin x + √(1 - x^2) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_16_b : ∀ f f_inv F c,
  inverse f f_inv ->
  differentiable f_inv ->
  (∀ x, ⟦ der x ⟧ F = f) ->
  ∫ (λ x, f_inv x) = (λ x, x * f_inv x - F (f_inv x) + c).
Proof.
Abort.
