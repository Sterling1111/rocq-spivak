From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_15 : ∀ a b,
  a > 1 -> b > 1 ->
  ∫ 1 a (λ t, 1 / t) + ∫ 1 b (λ t, 1 / t) = ∫ 1 (a * b) (λ t, 1 / t).
Abort.
