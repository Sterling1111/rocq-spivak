From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_32_c : ∀ φ₁ φ₂ g₁ g₂ a b,
  a < b ->
  (∀ x, x ∈ (a, b) -> g₂ x > g₁ x) ->
  (∀ x, ⟦ der x ⟧ (⟦ Der ⟧ φ₁) = (λ x, - g₁ x * φ₁ x)) ->
  (∀ x, ⟦ der x ⟧ (⟦ Der ⟧ φ₂) = (λ x, - g₂ x * φ₂ x)) ->
  (∀ x, x ∈ (a, b) -> φ₂ x <> 0) ->
  ~ (φ₁ a = 0 /\ φ₁ b = 0).
Abort.
