From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_31_a :
  ⟦ lim ∞ ⟧ (λ x, exp (-x^2) * ∫ 0 x (λ t, exp (t^2))) = 0.
Abort.

Lemma lemma_18_31_b_i :
  ⟦ lim ∞ ⟧ (λ x, exp (-x^2) * ∫ x (x + 1/x) (λ t, exp (t^2))) = 0.
Abort.

Lemma lemma_18_31_b_ii :
  ⟦ lim ∞ ⟧ (λ x, exp (-x^2) * ∫ x (x + log x / x) (λ t, exp (t^2))) = ∞.
Abort.

Lemma lemma_18_31_b_iii :
  ⟦ lim ∞ ⟧ (λ x, exp (-x^2) * ∫ x (x + log x / (2*x)) (λ t, exp (t^2))) = 1/2.
Abort.
