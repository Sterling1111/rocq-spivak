From Calculus.Chapter19 Require Import Prelude.

Section section_19_26.

Variable φ : ℝ -> ℝ.

Hypothesis H1 : integrable φ.
Hypothesis H2 : nonnegative φ.
Hypothesis H3 : ∀ x, |x| >= 1 -> φ x = 0.
Hypothesis H4 : ∫ (-1) 1 φ = 1.

Definition φ_ (h x : ℝ) := 1 / h * φ (x / h).

Lemma lemma_19_26_a : ∀ h, h > 0 ->
  (∀ x, |x| >= h -> φ_ h x = 0) /\
  ∫ (-h) h (φ_ h) = 1.
Abort.

Lemma lemma_19_26_b : ∀ f,
  integrable_on (-1) 1 f -> continuous_at f 0 ->
  ⟦ lim 0⁺ ⟧ (λ h, ∫ (-1) 1 (λ x, φ_ h x * f x)) = f 0 /\
  ⟦ lim 0⁺ ⟧ (λ h, ∫ (-h) h (λ x, φ_ h x * f x)) = f 0.
Abort.

End section_19_26.

Lemma lemma_19_26_c :
  ⟦ lim 0⁺ ⟧ (λ h, ∫ (-1) 1 (λ x, h/(h^2+x^2))) = π.
Abort.

Lemma lemma_19_26_d : ∀ f, integrable_on (-1) 1 f -> continuous_at f 0 ->
  ⟦ lim 0⁺ ⟧ (λ h, ∫ (-1) 1 (λ x, h/(h^2+x^2)*f x)) = π*f 0.
Abort.
