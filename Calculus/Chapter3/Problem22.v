From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_22_a : ∀ f g h : R -> R,
  g = h ∘ f -> ∀ x y, f x = f y -> g x = g y.
Proof.
  intros f g h H1 x y H2. subst g. unfold compose. rewrite H2. reflexivity.
Qed.

Lemma lemma_3_22_b : ∀ f g : R -> R,
  (∀ x y, f x = f y -> g x = g y) -> ∃ h : R -> R, g = h ∘ f.
Proof.
  intros f g H1.
  set (h := λ z, if excluded_middle_informative (∃ x, f x = z)
    then g (epsilon (inhabits 0) (λ x, f x = z)) else 0).
  exists h. apply functional_extensionality. intro x. unfold compose, h.
  destruct (excluded_middle_informative (∃ y, f y = f x)) as [H2 | H2].
  - apply H1. symmetry. apply epsilon_spec. exact H2.
  - exfalso. apply H2. exists x. reflexivity.
Qed.
