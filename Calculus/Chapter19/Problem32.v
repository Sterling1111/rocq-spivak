From Calculus.Chapter19 Require Import Prelude.

From Calculus.Chapter19 Require Import Problem29.
Lemma lemma_19_32_a : ∀ a, 0 < a ->
  has_length_19 (λ t, a*(t-sin t)) (λ t, a*(1-cos t)) 0 (2*π) (8*a).
Abort.

Lemma lemma_19_32_b : ∀ a, 0 < a ->
  ∫ 0 (2*π) (λ t, a*(1-cos t) * (a*(1-cos t))) = 3*π*a^2.
Abort.
