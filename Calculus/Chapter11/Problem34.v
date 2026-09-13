From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_34_b : ∀ f f' L1 L2,
  ⟦ lim ∞ ⟧ f = L1 ->
  ⟦ lim ∞ ⟧ f' = L2 ->
  (∃ M, ∀ x, x > M -> ⟦ der x ⟧ f = f') ->
  L2 = 0.
Proof.
  intros f f' L1 L2 H1 H2 [M H3].
  destruct (Req_dec L2 0) as [H4 | H4]; auto.
  assert (H5 : |L2| > 0) by solve_R.
  destruct (H1 (|L2| / 8) ltac:(lra)) as [N1 H6].
  destruct (H2 (|L2| / 4) ltac:(lra)) as [N2 H7].
  set (a := Rmax M (Rmax N1 N2) + 1).
  assert (H8 : continuous_on f [a, a + 1]).
  {
    apply continuous_at_imp_continuous_on. intros x H8.
    apply differentiable_at_imp_continuous_at, derivative_at_imp_differentiable_at with (f' := f').
    apply H3. unfold a in H8. solve_R.
  }
  assert (H9 : differentiable_on f (a, a + 1)).
  {
    apply derivative_on_imp_differentiable_on with (f' := f').
    apply derivative_at_imp_derivative_on; [apply differentiable_domain_open; lra |].
    intros x H9. apply H3. unfold a in H9. solve_R.
  }
  pose proof mean_value_theorem f a (a + 1) ltac:(lra) H8 H9 as [c [H10 H11]].
  pose proof derivative_at_unique f _ _ c (H3 c ltac:(unfold a in *; solve_R)) H11 as H12.
  specialize (H7 c ltac:(unfold a in *; solve_R)).
  pose proof H6 a ltac:(unfold a; solve_R) as H13.
  specialize (H6 (a + 1) ltac:(unfold a; solve_R)).
  simpl in H12. replace (a + 1 - a) with 1 in H12 by lra. field_simplify in H12.
  solve_R.
Qed.

Lemma lemma_11_34_c : ∀ f f'' L1 L2,
  ⟦ lim ∞ ⟧ f = L1 ->
  ⟦ lim ∞ ⟧ f'' = L2 ->
  (∃ M, ∀ x, x > M -> ⟦ der ^ 2 x ⟧ f = (λ _, f'' x)) ->
  L2 = 0.
Proof.
  intros f f'' L1 L2 H1 H2 [M H3].
  set (f' := λ x, ⟦ Der x ⟧ f).
  assert (H4 : ∀ x, x > M -> ⟦ der x ⟧ f = f' /\ ⟦ der x ⟧ f' = f'').
  {
    intros x H4. destruct (H3 x H4) as [δ [g [H5 [H6 H7]]]].
    assert (H8 : ∀ y, y ∈ (x - δ, x + δ) -> f' y = g y).
    {
      intros y H8. unfold f'.
      exact (nth_derivative_on_open_imp_nth_derive_eq 1 f g (x - δ, x + δ)
        ltac:(intros z H9; auto_interval) H6 y H8).
    }
    split.
    - destruct H6 as [f0 [H6 H9]].
      apply derivative_at_ext_val with (f' := g); [| symmetry; apply H8; solve_R].
      apply derivative_at_eq with (f1 := f0).
      + exists δ. split; auto. intros y H10. symmetry. apply H6. solve_R.
      + apply derivative_on_imp_derivative_at with (D := (x - δ, x + δ)); auto_interval.
    - apply derivative_at_ext_val with (f' := λ _, f'' x); [| reflexivity].
      apply derivative_at_eq with (f1 := g); auto.
      exists δ. split; auto. intros y H9. symmetry. apply H8. solve_R.
  }
  assert (H5 : ∀ g g' u v,
    M < u -> u < v ->
    (∀ x, x > M -> ⟦ der x ⟧ g = g') ->
    ∃ c, u < c < v /\ g' c = (g v - g u) / (v - u)).
  {
    intros g g' u v H5 H6 H7.
    assert (H8 : continuous_on g [u, v]).
    {
      apply continuous_at_imp_continuous_on. intros x H8.
      apply differentiable_at_imp_continuous_at, derivative_at_imp_differentiable_at with (f' := g').
      apply H7. solve_R.
    }
    assert (H9 : differentiable_on g (u, v)).
    {
      apply derivative_on_imp_differentiable_on with (f' := g').
      apply derivative_at_imp_derivative_on; [apply differentiable_domain_open; auto |].
      intros x H9. apply H7. solve_R.
    }
    pose proof mean_value_theorem g u v H6 H8 H9 as [c [H10 H11]].
    exists c. split; auto. exact (derivative_at_unique g _ _ c (H7 c ltac:(solve_R)) H11).
  }
  destruct (Req_dec L2 0) as [H6 | H6]; auto.
  assert (H7 : |L2| > 0) by solve_R.
  destruct (H1 (|L2| / 16) ltac:(lra)) as [N1 H8].
  destruct (H2 (|L2| / 4) ltac:(lra)) as [N2 H9].
  set (a := Rmax M (Rmax N1 N2) + 1).
  pose proof H5 f f' a (a + 1) ltac:(unfold a; solve_R) ltac:(lra)
    ltac:(intros x H10; apply H4; auto) as [c1 [H10 H11]].
  pose proof H5 f f' (a + 2) (a + 3) ltac:(unfold a; solve_R) ltac:(lra)
    ltac:(intros x H12; apply H4; auto) as [c2 [H12 H13]].
  pose proof H5 f' f'' c1 c2 ltac:(unfold a in *; solve_R) ltac:(lra)
    ltac:(intros x H14; apply H4; auto) as [c [H14 H15]].
  pose proof H8 a ltac:(unfold a; solve_R) as H16.
  pose proof H8 (a + 1) ltac:(unfold a; solve_R) as H17.
  pose proof H8 (a + 2) ltac:(unfold a; solve_R) as H18.
  specialize (H8 (a + 3) ltac:(unfold a; solve_R)).
  specialize (H9 c ltac:(unfold a in *; solve_R)).
  replace (a + 1 - a) with 1 in H11 by lra.
  replace (a + 3 - (a + 2)) with 1 in H13 by lra.
  field_simplify in H11. field_simplify in H13.
  apply Rmult_eq_compat_r with (r := c2 - c1) in H15. field_simplify in H15; try lra.
  solve_abs.
Qed.
