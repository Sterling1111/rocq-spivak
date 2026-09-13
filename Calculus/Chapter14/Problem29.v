From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_29_a : ∀ f,
  continuous_on f [0, 1] ->
  ⟦ lim 0⁺ ⟧ (λ x, x * ∫ x 1 (λ t, f t / t)) = f 0.
Abort.

Lemma lemma_14_29_b : ∀ f,
  integrable_on 0 1 f ->
  continuous_at f 0 ->
  ⟦ lim 0⁺ ⟧ (λ x, x * ∫ x 1 (λ t, f t / t^2)) = f 0.
Abort.
