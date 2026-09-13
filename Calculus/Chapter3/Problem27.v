From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_27_a : ∃ g : R -> R,
  (λ x, x + 1) ∘ g = g ∘ (λ x, x + 1).
Proof.
  exists (λ x, x). reflexivity.
Qed.

Lemma lemma_3_27_b : ∀ (c : R) (g : R -> R),
  (λ _ : R, c) ∘ g = g ∘ (λ _ : R, c) <-> g c = c.
Proof.
  intros c g. split.
  - intro H1. pose proof (f_equal (λ h, h 0) H1) as H2. symmetry. exact H2.
  - intro H1. apply functional_extensionality. intro x. unfold compose. symmetry. exact H1.
Qed.

Lemma lemma_3_27_c : ∀ f : R -> R, 
  (∀ g : R -> R, f ∘ g = g ∘ f) -> ∀ x, f x = x.
Proof.
  intros f H1 x. specialize (H1 (λ _, x)).
  exact (f_equal (λ h, h 0) H1).
Qed.
