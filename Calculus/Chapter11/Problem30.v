From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_30_a : forall f g f' g' a x,
  ⟦ der ⟧ f = f' -> 
  ⟦ der ⟧ g = g' ->
  (∀ x, f' x > g' x) ->
  f a = g a ->
  (x > a -> f x > g x) /\ (x < a -> f x < g x).
Proof.
  intros f g f' g' a x H1 H2 H3 H4.
  set (h := (f - g)%function).
  assert (forall u v, u < v -> continuous_on h [u, v]) as H5.
  {
    intros u v H6.
    apply continuous_imp_continuous_on, differentiable_imp_continuous, 
    derivative_imp_differentiable with (f' := (f' - g')%function).
    unfold h; auto_diff.
  }
  assert (forall u v, u < v -> differentiable_on h (u, v)) as H6.
  {
    intros u v H7.
    apply differentiable_imp_differentiable_on.
    - unfold h; apply derivative_imp_differentiable with (f' := (f' - g')%function); auto_diff.
    - apply differentiable_domain_open, H7.
  }
  split; intros H7.
  - pose proof mean_value_theorem h a x H7 (H5 a x H7) (H6 a x H7) as [y [H8 H9]].
    assert (⟦ der y ⟧ h = f' - g') as H10 by (unfold h; auto_diff).
    pose proof derivative_at_unique h (λ _ : ℝ, (h x - h a) / (x - a)) (f' - g') y H9 H10 as H11.
    simpl in H11; unfold h in *.
    rewrite H4 in H11.
    apply Rmult_eq_compat_r with (r := (x - a)) in H11.
    field_simplify in H11; try lra.
    specialize (H3 y).
    nra.
  - pose proof mean_value_theorem h x a H7 (H5 x a H7) (H6 x a H7) as [y [H8 H9]].
    assert (⟦ der y ⟧ h = f' - g') as H10 by (unfold h; auto_diff).
    pose proof derivative_at_unique h (λ _ : ℝ, (h a - h x) / (a - x)) (f' - g') y H9 H10 as H11.
    simpl in H11; unfold h in *.
    rewrite <- H4 in H11.
    apply Rmult_eq_compat_r with (r := (a - x)) in H11.
    field_simplify in H11; try lra.
    specialize (H3 y).
    nra.
Qed.

Lemma lemma_11_30_c : forall f f' g g' a x0,
  differentiable f -> differentiable g ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  f a = g a ->
  (forall x, f' x >= g' x) ->
  x0 > a ->
  f' x0 > g' x0 ->
  (forall x, x >= x0 -> f x > g x).
Abort.
