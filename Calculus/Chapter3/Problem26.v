From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_26 : ∀ f g h : R -> R,
  f ∘ g = (λ x, x) -> h ∘ f = (λ x, x) -> g = h.
Proof.
  intros f g h H1 H2. apply functional_extensionality. intros x.
  pose proof (f_equal (λ k, k x) H1) as H3.
  pose proof (f_equal (λ k, k (g x)) H2) as H4.
  unfold compose in *. simpl in *. rewrite H3 in H4. symmetry. exact H4.
Qed.
