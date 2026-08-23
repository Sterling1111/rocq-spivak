From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_9 : forall f x,
  continuous f ->
  ∫ 0 x (λ u, f u * (x - u)) = ∫ 0 x (λ u, ∫ 0 u f).
Proof.
  intros f x H1.
  set (F := λ u, ∫ 0 u f).
  set (g := λ u, x - u).
  set (g' := λ _ : ℝ, -1).
  set (U := λ z, ∫ 0 z (f ⋅ g)).

  assert (H2 : ⟦ der ⟧ F = f).
  { unfold F. apply FTC1_global. exact H1. }

  assert (H3 : ⟦ der ⟧ g = g').
  { unfold g, g'. auto_diff. }

  assert (H4 : continuous g').
  { unfold g'. auto_cont. }

  assert (H5 : continuous g).
  { unfold g. auto_cont. }

  assert (H6 : ⟦ der ⟧ U = (f ⋅ g)).
  { unfold U. apply FTC1_global. auto_cont. }

  pose proof integration_by_parts_definite F g f g' U 0 x H1 H4 H2 H3 H6 as H7.

  assert (H8 : continuous F).
  {
    apply differentiable_imp_continuous.
    apply derivative_imp_differentiable with (f' := f).
    exact H2.
  }

  assert (H9 : integrable_on (Rmin 0 x) (Rmax 0 x) F).
  {
    apply theorem_13_3; solve_R;
    apply continuous_imp_continuous_on;
    auto.
  }

  replace (F ⋅ g') with (-1 * F)%function in H7.
  2 : { extensionality u. unfold g'. lra. }

  rewrite integral_mult_scalar' in H7; auto.

  replace (F 0) with 0 in * by (unfold F; rewrite integral_n_n; auto).

  replace (g x) with 0 in * by (unfold g; lra).

  lra.
Qed.