From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_22_a : forall n c,
  (n > 0)%nat ->
  ∫ (λ x, x^n * exp x) = (λ x, x^n * exp x - INR n * ∫ (λ x, x^(n-1) * exp x) x + c).
Abort.

Lemma lemma_19_22_b : forall n c,
  (n > 0)%nat ->
  ∫ (λ x, (log x)^n) = (λ x, x * (log x)^n - INR n * ∫ (λ x, (log x)^(n-1)) x + c).
Abort.
