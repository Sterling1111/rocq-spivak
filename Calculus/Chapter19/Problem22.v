From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_22_a : ∀ (n : nat) c, (0 < n)%nat ->
  ∫ (λ x, x^n * exp x) =
    (λ x, x^n*exp x - n * ∫ 0 x (λ t, t^(n-1)*exp t) + c).
Proof.
  intros n c H1.
Abort.

Lemma lemma_19_22_b : ∀ (n : nat) c, (0 < n)%nat ->
  ∫ (λ x, log x^n) (0, ∞) =
    (λ x, x*log x^n - n * ∫ 1 x (λ t, log t^(n-1)) + c).
Abort.
