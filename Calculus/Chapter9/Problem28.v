From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_28_a : ∀ f,
  f = (λ x, |x|^3) ->
  ⟦ der ⟧ f = (λ x, 3 * x * |x|) /\
  ⟦ der ^ 2 ⟧ f = (λ x, 6 * |x|) /\
  ~ differentiable_at (λ x, ⟦ Der ^ 2 x ⟧ f) 0.
Proof.

Admitted.

Lemma lemma_9_28_b : ∀ f,
  (∀ x, x >= 0 -> f x = x^4) ->
  (∀ x, x <= 0 -> f x = -x^4) ->
  ⟦ der ⟧ f = (λ x, 4 * |x| ^ 3) /\
  ⟦ der ^ 2 ⟧ f = (λ x, 12 * x * |x|) /\
  ⟦ der ^ 3 ⟧ f = (λ x, 24 * |x|) /\
  ~ differentiable_at (λ x, ⟦ Der ^ 3 x ⟧ f) 0.
Proof.

Admitted.