From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_18 : ∀ c,
  ∫ (λ x, log (log x)) (1, ∞) =
    (λ x, x * log (log x) - ∫ 2 x (λ t, 1 / log t) + c).
Proof.
Abort.