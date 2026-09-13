From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_6 : ∀ x,
  x > 0 ->
  ∫ 0 x (λ t, sin t / (t + 1)) > 0.
Abort.
