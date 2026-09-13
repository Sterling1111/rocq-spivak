From Calculus.Chapter3 Require Export Prelude.
From Calculus.Chapter3 Require Import Problem22.

Lemma lemma_3_24_a : ∀ g : R -> R,
  (∀ x y, x <> y -> g x <> g y) -> ∃ f : R -> R, f ∘ g = (λ x, x).
Proof.
  intros g H1.
  destruct (lemma_3_22_b g (λ x, x)) as [f H2].
  - intros x y H2. destruct (Req_dec x y) as [H3 | H3]; auto.
    exfalso. apply (H1 x y H3). exact H2.
  - exists f. symmetry. exact H2.
Qed.

Lemma lemma_3_24_b : ∀ f : R -> R,
  (∀ b, ∃ a, b = f a) -> ∃ g : R -> R, f ∘ g = (λ x, x).
Proof.
  intros f H1.
  exists (λ b, epsilon (inhabits 0) (λ a, b = f a)).
  apply functional_extensionality. intro b. unfold compose.
  symmetry. apply epsilon_spec. apply H1.
Qed.
