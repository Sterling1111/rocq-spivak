From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_64 : ∀ f f',
  f 0 = 0 ->
  ⟦ der ⟧ f = f' ->
  increasing f' ->
  increasing_on (λ x, f x / x) (0, ∞).
Proof.
  intros f f' H1 H2 H3.
  set (g := λ x, f x / x).
  set (g' := λ x, (x * f' x - f x) / x^2).
  assert (H4 : ∀ x, x > 0 -> g' x > 0).
  {
    intros x H4.
    assert (H5 : continuous_on f [0, x]).
    { apply continuous_imp_continuous_on, differentiable_imp_continuous, derivative_imp_differentiable with (f' := f'); auto. }
    assert (H6 : differentiable_on f (0, x)).
    { apply derivative_on_imp_differentiable_on with (f' := f'); auto_diff. }
    pose proof mean_value_theorem f 0 x H4 H5 H6 as [c [H7 H8]].
    pose proof derivative_at_unique f _ _ c (H2 c) H8 as H9.
    pose proof H3 c x ltac:(solve_R) ltac:(solve_R) ltac:(solve_R) as H10.
    simpl in H9. rewrite H1, !Rminus_0_r in H9.
    apply Rmult_eq_compat_r with (r := x) in H9. field_simplify in H9; try lra.
    unfold g'. apply Rdiv_pos_pos; nra.
  }
  intros x y H5 H6 H7.
  apply derivative_on_pos_imp_increasing_on_open with (f' := g') (a := x) (b := y); try solve [solve_R].
  - unfold g. auto_cont.
  - unfold g, g'. auto_diff.
  - intros z H8. apply H4. solve_R.
Qed.
