From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_43_a_parts : ∀ a b, 0 < a < b ->
  ∫ a b (λ x, sin x/x) = cos a/a - cos b/b - ∫ a b (λ x, cos x/x^2).
Abort.

Lemma lemma_19_43_a : ∃ I, improper_positive_19 (λ x, sin x/x) I.
Abort.

Lemma lemma_19_43_b : ∀ n : nat,
  ∫ 0 π (λ t, sin ((n+1/2)*t)/sin (t/2)) = π.
Abort.

Lemma lemma_19_43_c : limit_pinf
  (λ k, ∫ 0 π (λ t, sin ((k+1/2)*t)*(2/t - 1/sin (t/2)))) 0.
Abort.

Lemma lemma_19_43_d : improper_positive_19 (λ x, sin x/x) (π/2).
Abort.
