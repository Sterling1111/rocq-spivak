From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_50 : ∀ f f' g g' a b,
  a < b ->
  continuous_on f [a, b] -> continuous_on g [a, b] ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  (∀ x, x ∈ (a, b) -> g' x <> 0) ->
  ∃ x, x ∈ (a, b) /\ f' x / g' x = (f x - f a) / (g b - g x).
Proof.
  intros f f' g g' a b H1 H2 H3 H4 H5 H6.
  set (h := λ x, f x * g b + g x * f a - f x * g x).
  set (h' := λ x, f' x * g b + g' x * f a - (f' x * g x + f x * g' x)).
  assert (H7 : continuous_on h [a, b]).
  {
    unfold h. apply continuous_on_minus.
    - apply continuous_on_plus; apply continuous_on_mult; auto; apply continuous_on_const.
    - apply continuous_on_mult; auto.
  }
  assert (H8 : ⟦ der ⟧ h (a, b) = h').
  {
    apply derivative_at_imp_derivative_on; [apply differentiable_domain_open; auto |].
    intros x H8.
    pose proof derivative_on_imp_derivative_at f f' (a, b) x ltac:(auto_interval) H4 as H9.
    pose proof derivative_on_imp_derivative_at g g' (a, b) x ltac:(auto_interval) H5 as H10.
    unfold h, h'. auto_diff.
  }
  pose proof rolles_theorem h a b H1 H7
    ltac:(apply derivative_on_imp_differentiable_on with (f' := h'); auto)
    ltac:(unfold h; ring) as [x [H9 H10]].
  pose proof derivative_on_imp_derivative_at h h' (a, b) x ltac:(auto_interval) H8 as H11.
  pose proof derivative_at_unique h _ _ x H11 H10 as H12.
  assert (H13 : g b <> g x).
  {
    intros H13.
    assert (H14 : continuous_on g [x, b]).
    { apply continuous_on_subset with (A2 := [a, b]); auto. intros y H14; solve_R. }
    assert (H15 : differentiable_on g (x, b)).
    {
      apply derivative_on_imp_differentiable_on with (f' := g').
      apply derivative_on_subset with (D1 := (a, b)); auto.
      - apply differentiable_domain_open; solve_R.
      - intros y H15; solve_R.
    }
    pose proof rolles_theorem g x b ltac:(solve_R) H14 H15 ltac:(lra) as [c [H16 H17]].
    pose proof derivative_on_imp_derivative_at g g' (a, b) c ltac:(auto_interval) H5 as H18.
    pose proof derivative_at_unique g _ _ c H18 H17 as H19.
    specialize (H6 c ltac:(solve_R)). simpl in H19. contradiction.
  }
  exists x. split; auto. specialize (H6 x H9). unfold h' in H12. simpl in H12. solve_R.
Qed.
