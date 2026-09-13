From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_17_a : ∀ c,
  ∫ (λ x, (sin x)^4) = (λ x, 3*x/8 - sin (2*x) / 4 + sin (4*x) / 32 + c).
Proof.
  auto_int.
Abort.

Lemma lemma_19_17_b : ∀ x,
  (sin x)^4 = 3/8 - cos (2*x) / 2 + cos (4*x) / 8.
Abort.

Lemma lemma_19_17_a_reduction : ∀ c,
  ∫ (λ x, sin x^4) =
    (λ x, -sin x^3*cos x/4 + 3/8*(x-sin x*cos x) + c).
Abort.

Lemma lemma_19_17_b_identity : ∀ x,
  -sin x^3*cos x/4 - 3*sin x*cos x/8 =
  -sin (2*x)/4 + sin (4*x)/32.
Abort.
