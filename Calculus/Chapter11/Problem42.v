From Calculus.Chapter11 Require Import Prelude.
From Calculus.Chapter11 Require Import Problem30.

Lemma lemma_11_42_a : forall f f' f'',
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  f 0 = 0 -> f 1 = 1 ->
  f' 0 = 0 -> f' 1 = 0 ->
  exists x, x ∈ (0, 1) /\ |f'' x| >= 4.
Proof.
  intros f f' f'' H1 H2 H3 H4 H5 H6.
  apply NNPP.
  intros H7.
  assert (H8 : forall x, x ∈ (0, 1) -> |f'' x| < 4).
  {
    intros x H8.
    apply Rnot_ge_lt.
    intros H9.
    apply H7.
    exists x.
    split; assumption.
  }
  assert (H9 : forall x, x ∈ (0, 1/2] -> f' x < 4 * x).
  {
    intros x H9.
    assert (H10 : 0 < x) by solve_R.
    assert (H11 : continuous_on f' [0, x]).
    {
      apply continuous_imp_continuous_on, differentiable_imp_continuous,
      derivative_imp_differentiable with (f' := f''); auto.
    }
    assert (H12 : differentiable_on f' (0, x)).
    {
      apply differentiable_imp_differentiable_on.
      - eapply derivative_imp_differentiable; eauto.
      - apply differentiable_domain_open; auto.
    }
    pose proof mean_value_theorem f' 0 x H10 H11 H12 as [x' [H13 H14]].
    pose proof derivative_at_unique f' f'' (λ _, (f' x - f' 0) / (x - 0)) x' (H2 x') H14 as H16.
    simpl in H16.
    rewrite H5 in H16.
    specialize (H8 x' ltac:(solve_R)).
    repeat rewrite Rminus_0_r in H16.
    apply Rmult_eq_compat_r with (r := x) in H16.
    field_simplify in H16; solve_R.
  }
  assert (H10 : f (1/2) < 1/2).
  {
    assert (H10 : (∀ c : ℝ, c ∈ (0, 1 / 2) ∨ c ∈ (1 / 2, 0) → (λ x : ℝ, 4 * x) c > f' c)).
    { intros c H10. specialize (H9 c); solve_R. }
    pose proof lemma_11_30_a' (fun x => 2 * x^2) f (fun x => 4 * x) f' 0 (1/2) ltac:(auto_diff) H1 ltac:(simpl; lra) H10 as [H12 _].
    solve_R.
  }
  set (g := fun x => 1 - f (1 - x)).
  assert (H11 : ⟦ der ⟧ g = λ x, f' (1 - x)) by (unfold g; auto_diff).

  assert (H12 : forall x, x ∈ (0, 1 / 2] -> f' (1 - x) < 4 * x).
  {
    intros x' H12.
    assert (H13 : continuous_on f' [1 - x', 1]).
    { apply continuous_imp_continuous_on, differentiable_imp_continuous, derivative_imp_differentiable with (f' := f''); auto. }
    assert (H14 : differentiable_on f' (1 - x', 1)).
    {
      apply differentiable_imp_differentiable_on.
      - apply derivative_imp_differentiable with (f' := f''). exact H2.
      - apply differentiable_domain_open. solve_R.
    }
    pose proof mean_value_theorem f' (1 - x') 1 ltac:(solve_R) H13 H14 as [c [H15 H16]].
    pose proof derivative_at_unique f' f'' (fun _ => (f' 1 - f' (1 - x')) / (1 - (1 - x'))) c (H2 c) H16 as H17.
    simpl in H17. rewrite H6 in H17.
    specialize (H8 c ltac:(solve_R)).
    apply Rmult_eq_compat_r with (r := 1 - (1 - x')) in H17. field_simplify in H17; solve_R.
  }

  assert (H13 : g (1/2) < 1/2).
  {
    assert (H13 : (∀ c : ℝ, c ∈ (0, 1 / 2) ∨ c ∈ (1 / 2, 0) → (λ x : ℝ, 4 * x) c > f' (1 - c))).
    { intros c H13. specialize (H12 c); solve_R. }
    assert (H14 : (λ x : ℝ, 2 * x ^ 2) 0 = g 0).
    { unfold g. simp_zero. lra. }
    pose proof lemma_11_30_a' (fun x => 2 * x^2) g (fun x => 4 * x) (fun x => f' (1 - x)) 0 (1/2) ltac:(auto_diff) H11 H14 H13 as [H15 _].
    solve_R.
  }
  unfold g in H13.
  replace (1 - 1 / 2) with (1 / 2) in H13 by lra.
  lra.
Qed.