From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_15_a : ~ (∀ f g a, differentiable_at (λ x, f x + g x) a -> differentiable_at f a /\ differentiable_at g a).
Proof.
  intros H1.
  set (f := λ x, |x|).
  set (g := λ x, -|x|).
  specialize (H1 f g 0).

  assert (H2 : (f + g)%function = λ _, 0).
  { extensionality x. unfold f, g. lra. }

  rewrite H2 in H1.

  assert (H3 : differentiable_at (λ _ : ℝ, 0) 0).
  { apply derivative_at_imp_differentiable_at with (f' := λ _, 0). auto_diff. }

  specialize (H1 H3) as [[L1 H1] _].

  assert (H4 : ⟦ lim 0⁺ ⟧ (λ h, (f (0 + h) - f 0) / h) = 1).
  {
    unfold f. apply limit_right_eq with (f1 := λ _, 1); try auto_limit.
    exists 1. split; solve_R.
  }
  assert (H5 : ⟦ lim 0⁻ ⟧ (λ h, (f (0 + h) - f 0) / h) = -1).
  {
    unfold f. apply limit_left_eq with (f1 := λ _, -1); try auto_limit.
    exists 1. split; solve_R.
  }

  apply limit_iff in H1 as [H1 H6].

  pose proof (limit_right_unique _ _ _ _ H6 H4).
  pose proof (limit_left_unique _ _ _ _ H1 H5).
  lra.
Qed.

Lemma lemma_10_15_b : ∀ f g a,
  differentiable_at f a ->
  f a ≠ 0 ->
  differentiable_at (λ x, f x * g x) a ->
  differentiable_at g a.
Proof. 
  intros f g a H1 H2 H3.

  set (h := f ⋅ g).

  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H3 as [h' H3].

  apply derivative_at_imp_differentiable_at with (f' := fun x => (h' x * f x - f' x * h x) / (f x * f x)).

  assert (H4 : continuous_at f a).
  { apply differentiable_at_imp_continuous_at. exists (f' a). exact H1. }

  pose proof (continuous_at_locally_nonzero f a H4 H2) as [δ [H5 H6]].
  apply derivative_at_eq with (f1 := fun x => h x / f x).
  - exists δ. split; auto.
    intros x H7.
    specialize (H6 x H7).
    unfold h. 
    field. 
    exact H6.
  - apply derivative_at_div; auto.
Qed.