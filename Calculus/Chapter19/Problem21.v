From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_21_a : forall n c,
  (n >= 2)%nat ->
  ∫ (λ x, (sin x)^n) = (λ x, -(sin x)^(n-1) * cos x / INR n + INR (n-1) / INR n * ∫ (λ x, (sin x)^(n-2)) x + c).
Abort.

Lemma lemma_19_21_b : forall n c,
  (n >= 2)%nat ->
  ∫ (λ x, (cos x)^n) = (λ x, (cos x)^(n-1) * sin x / INR n + INR (n-1) / INR n * ∫ (λ x, (cos x)^(n-2)) x + c).
Abort.
