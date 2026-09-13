From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_5_i : ∃ g : R -> R,
  ∀ x, ∫ 0 x (λ t, t * g t) = x + x^2.
Abort.

Lemma lemma_14_5_ii : ∃ g : R -> R,
  ∀ x, ∫ 0 (x^2) (λ t, t * g t) = x + x^2.
Abort.
