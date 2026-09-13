From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_23 : ∀ x,
  x >= 0 ->
  ∫ 1 (cosh x) (λ t, √(t^2 - 1)) = (cosh x * sinh x) / 2 - x / 2.
Abort.
