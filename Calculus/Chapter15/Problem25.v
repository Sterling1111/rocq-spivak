From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_25 : forall x y,
  x <> y ->
  |sin x - sin y| < |x - y|.
Proof.
  assert (H1 : forall a b, a < b -> |sin a - sin b| < b - a).
  { intros a b H2.
    assert (H3 : exists z, a < z /\ z < b /\ forall w, a < w -> w < z -> |cos w| < 1).
    { apply lemma_cos_lt_1_exists_z; auto. }
    destruct H3 as [z [H4 [H5 H6]]].
    assert (H7 : differentiable_on sin (a, z)). { apply derivative_on_imp_differentiable_on with (f' := cos); auto_diff. }
    pose proof mean_value_theorem sin a z H4 ltac:(auto_cont) H7 as [θ1 [H8 H9]].
    assert (H10 : differentiable_on sin (z, b)). { apply derivative_on_imp_differentiable_on with (f' := cos); auto_diff. }
    pose proof mean_value_theorem sin z b H5 ltac:(auto_cont) H10 as [θ2 [H11 H12]].
    assert (H13 : cos θ1 = (sin z - sin a) / (z - a)).
    { apply (derivative_at_unique sin (λ _, cos θ1) (λ _, (sin z - sin a) / (z - a)) θ1); auto_diff. }
    assert (H14 : cos θ2 = (sin b - sin z) / (b - z)).
    { apply (derivative_at_unique sin (λ _, cos θ2) (λ _, (sin b - sin z) / (b - z)) θ2); auto_diff. }
    apply Rmult_eq_compat_r with (r := z - a) in H13; field_simplify in H13; try lra.
    apply Rmult_eq_compat_r with (r := b - z) in H14; field_simplify in H14; try lra.
    assert (H15 : |cos θ1| < 1). { apply H6; solve_R. }
    assert (H16 : |cos θ2| <= 1) by (pose proof cos_bounds θ2; solve_R).
    assert (H17 : - (z - a) < sin z - sin a < z - a).
    { rewrite <- H13. solve_R. }
    assert (H18 : - (b - z) <= sin b - sin z <= b - z).
    { rewrite <- H14. solve_R. }
    replace (sin a - sin b) with (- (sin z - sin a) - (sin b - sin z)) by lra.
    solve_R.
  }
  intros x y H2.
  assert (x < y \/ y < x) as [H3 | H3] by solve_R.
  - pose proof H1 x y H3; solve_R.
  - pose proof H1 y x H3; solve_R.
Qed.