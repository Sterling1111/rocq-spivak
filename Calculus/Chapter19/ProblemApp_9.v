From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_9 : ∀ h A,
  h > 0 -> A > 0 ->
  ∫ 0 h (λ y, A * (y / h)^2) = A * h / 3.
Abort.
