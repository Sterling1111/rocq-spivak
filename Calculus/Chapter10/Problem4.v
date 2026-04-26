From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_4_i : ∀ f f',
  f = (λ x, 1 / (x + 1)) -> 
  ⟦ der ⟧ f = f' -> 
  ∀ x, x <> -1 -> x <> -2 -> 
  f' (f x) = - (x + 1)^2 / (2 + x)^2.
Proof.
  intros f f' H1 H2 x H3 H4.
  assert (H5 : ⟦ der (f x) ⟧ f = (λ y, -1 / (y + 1)^2)).
  {
    subst f. auto_diff. intro H5.
    apply Rmult_eq_compat_r with (r := (x + 1)) in H5.
    field_simplify in H5; nra.
  }
  pose proof derivative_at_unique f f' (λ y, -1 / (y + 1)^2) (f x) (H2 (f x)) H5 as H6.
  rewrite H6, H1.
  solve_R.
Qed.

Lemma lemma_10_4_ii : ∀ f f', f = (λ x, sin x) -> ⟦ der ⟧ f = f' -> ∀ x, f' (f x) = cos (sin x).
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ x, cos x)) by (subst; auto_diff).
  rewrite (derivative_unique f f' (λ x, cos x) H2 H3), H1; auto.
Qed.

Lemma lemma_10_4_iii : ∀ f f', f = (λ x, x^2) -> ⟦ der ⟧ f = f' -> ∀ x, f' (f x) = 2 * x^2.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ x, 2 * x)) by (subst; auto_diff).
  rewrite (derivative_unique f f' (λ x, 2 * x) H2 H3), H1; field.
Qed.

Lemma lemma_10_4_iv : ∀ f f', f = (λ x, 17) -> ⟦ der ⟧ f = f' -> ∀ x, f' (f x) = 0.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ _ : ℝ, 0)) by (subst; auto_diff).
  rewrite (derivative_unique f f' (λ _ : ℝ, 0) H2 H3). reflexivity.
Qed.
