From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_25 : ∀ r,
  r > 0 ->
  2 * ∫ (-r) r (λ x, √(r^2 - x^2)) = π * r^2.
Proof.
  intros r H1.
  assert (H2 : ∫ (-r) r (λ x, √(r^2 - x^2)) = π / 2 * r^2).
  { admit. }
  lra.
Admitted.