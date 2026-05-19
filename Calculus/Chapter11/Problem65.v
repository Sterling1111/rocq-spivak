From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_65 : ∀ n x,
  (n > 1)%nat ->
  x > -1 ->
  x <> 0 ->
  (1 + x)^n > 1 + n * x.
Proof.
  intros n x H1 H2 H3.
  set (g := λ x, (1 + x)^n - (1 + n * x)).
  set (g' := λ x, n * (1 + x)^(n-1) - n).

  assert (H4 : g 0 = 0).
  { unfold g. simp_zero. rewrite pow1. lra. }

  assert (H5 : ⟦ der ⟧ g = g').
  { unfold g, g'; auto_diff. }
  
  assert (minimum_point_strict g (-1, ∞) 0) as [_ H7].
  {
    apply first_derivative_test_domain_strict_min with (f' := g').
    - solve_R.
    - apply derivative_on_imp_differentiable_on with (f' := g'); auto_diff.
    - auto_diff.
    - intros y H8 H9.
      unfold g'.
      assert (H10 : 0 < 1 + y < 1) by solve_R.
      assert (H11 : (1 + y)^(n-1) < 1).
      { apply Rpow_lt_1; auto; lia. }
      solve_R.
    - intros y H8 H9.
      unfold g'.
      assert (H10 : 1 < 1 + y) by lra.
      assert (H11 : 1 < (1 + y)^(n-1)).
      { apply Rlt_pow_R1; auto; lia. }
      solve_R.
    - solve_R.
  }
  specialize (H7 x H2 H3).
  rewrite H4 in H7.
  unfold g in H7. 
  nra.
Qed.