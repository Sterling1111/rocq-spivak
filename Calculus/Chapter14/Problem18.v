From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_18 : forall h f g f' g',
  continuous h ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (λ x, ∫ (f x) (g x) h) =
    (λ x, h (g x) * g' x - h (f x) * f' x).
Proof.
  intros h f g f' g' H1 H2 H3.

  set (H := λ y : ℝ, ∫ 0 y h).

  assert (H4 : ⟦ der ⟧ H = h).
  {
    unfold H.
    apply FTC1_global.
    exact H1.
  }

  replace (λ x : ℝ, ∫ (f x) (g x) h) with ((H ∘ g) - (H ∘ f))%function.
  2 : {
    extensionality x.
    unfold H.
    pose proof (integral_split_minus' h 0 (g x) (f x)) as H5.
    assert (H6 : integrable_on (Rmin 0 (Rmin (g x) (f x))) (Rmax 0 (Rmax (g x) (f x))) h).
    {
      apply theorem_13_3; [solve_R |].
      apply continuous_imp_continuous_on.
      exact H1.
    }
    specialize (H5 H6).
    unfold compose.
    lra.
  }

  replace (λ x, h (g x) * g' x - h (f x) * f' x) with (((h ∘ g) ⋅ g') - ((h ∘ f) ⋅ f'))%function by auto.
  auto_diff.
Qed.