From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_23_a : ∀ f g : R -> R,
  f ∘ g = (λ x, x) -> ∀ x y, x <> y -> g x <> g y.
Proof.
  intros f g H1 x y H2 H3.
  pose proof (f_equal (λ h, h x) H1) as H4.
  pose proof (f_equal (λ h, h y) H1) as H5.
  unfold compose in *. simpl in *. rewrite H3 in H4. congruence.
Qed.

Lemma lemma_3_23_b : ∀ f g : R -> R,
  f ∘ g = (λ x, x) -> ∀ b, ∃ a, b = f a.
Proof.
  intros f g H1 b. exists (g b).
  pose proof (f_equal (λ h, h b) H1) as H2. symmetry. exact H2.
Qed.
