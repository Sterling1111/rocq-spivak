From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_6 : ∀ f f' f'',
  ⟦ der ⟧ f [0, ∞) = f' ->
  ⟦ der ⟧ f' [0, ∞) = f'' ->
  (∀ x, x >= 0 -> f x > 0) ->
  decreasing_on f [0, ∞) ->
  f' 0 = 0 ->
  ∃ x, x > 0 /\ f'' x = 0.
Proof.
  intros f f' f'' H1 H2 H3 H4 H5.
  assert (H6 : ∀ g g' a b,
    ⟦ der ⟧ g [0, ∞) = g' -> 0 <= a -> a < b ->
    ∃ c, a < c < b /\ g' c = (g b - g a) / (b - a)).
  {
    intros g g' a b H6 H7 H8.
    assert (H9 : continuous_on g [a, b]).
    {
      apply differentiable_on_imp_continuous_on_closed; auto.
      apply derivative_on_imp_differentiable_on with (f' := g').
      apply derivative_on_subset with (D1 := [0, ∞)); auto.
      - apply differentiable_domain_closed; auto.
      - intros x H9; solve_R.
    }
    assert (H10 : differentiable_on g (a, b)).
    {
      apply derivative_on_imp_differentiable_on with (f' := g').
      apply derivative_on_subset with (D1 := [0, ∞)); auto.
      - apply differentiable_domain_open; auto.
      - intros x H10; solve_R.
    }
    pose proof mean_value_theorem g a b H8 H9 H10 as [c [H11 H12]].
    pose proof derivative_on_imp_derivative_at g g' [0, ∞) c ltac:(exists (c / 2); split; [solve_R | intros y H14; solve_R]) H6 as H13.
    exists c. split; auto. exact (derivative_at_unique g _ _ c H13 H12).
  }
  pose proof H6 f f' 0 1 H1 ltac:(lra) ltac:(lra) as [c [H7 H8]].
  pose proof H4 0 1 ltac:(solve_R) ltac:(solve_R) ltac:(lra) as H9.
  assert (H10 : f' c < 0) by (field_simplify in H8; lra).
  assert (H11 : ∃ d, c < d /\ f' c < f' d).
  {
    apply NNPP. intros H11.
    assert (H12 : ∀ y, c < y -> f' y <= f' c).
    { intros y H12. destruct (Rlt_dec (f' c) (f' y)); [exfalso; apply H11; exists y; auto | lra]. }
    set (d := c + (f c + 1) / (- f' c)).
    assert (H13 : c < d).
    { unfold d. pose proof H3 c ltac:(lra) as H13. assert (0 < (f c + 1) / (- f' c)) by (apply Rdiv_pos_pos; lra). lra. }
    pose proof H6 f f' c d H1 ltac:(lra) H13 as [y [H14 H15]].
    specialize (H12 y ltac:(lra)).
    apply Rmult_eq_compat_r with (r := d - c) in H15. field_simplify in H15; try lra.
    assert (H16 : f d - f c <= f' c * (d - c)) by nra.
    assert (H17 : f' c * (d - c) = - (f c + 1)) by (unfold d; field; lra).
    pose proof H3 d ltac:(lra) as H18. lra.
  }
  destruct H11 as [d [H11 H12]].
  assert (H13 : continuous_on f' [0, d]).
  {
    apply differentiable_on_imp_continuous_on_closed; try lra.
    apply derivative_on_imp_differentiable_on with (f' := f'').
    apply derivative_on_subset with (D1 := [0, ∞)); auto.
    - apply differentiable_domain_closed; lra.
    - intros x H13; solve_R.
  }
  pose proof continuous_on_interval_attains_minimum f' 0 d ltac:(lra) H13 as [x [H14 H15]].
  pose proof H15 c ltac:(solve_R) as H16.
  assert (H17 : x ∈ (0, d)).
  { assert (x = 0 \/ x = d \/ x ∈ (0, d)) as [H17 | [H17 | H17]] by solve_R; subst; auto; lra. }
  assert (H18 : minimum_point f' (0, d) x).
  { split; auto. intros y H18. apply H15. solve_R. }
  pose proof derivative_on_imp_derivative_at f' f'' [0, ∞) x ltac:(exists (x / 2); split; [solve_R | intros y H21; solve_R]) H2 as H19.
  pose proof derivative_at_minimum_point_zero f' 0 d x H18
    ltac:(apply derivative_at_imp_differentiable_at with (f' := f''); auto) as H20.
  exists x. split; [solve_R |]. exact (derivative_at_unique f' _ _ x H19 H20).
Qed.
