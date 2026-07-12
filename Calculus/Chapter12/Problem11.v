From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_11 : forall f f' f'' f_inv f_inv' f_inv'' x,
  inverse f f_inv ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ f_inv = f_inv' ->
  ⟦ der ⟧ f_inv' = f_inv'' ->
  f' (f_inv x) <> 0 ->
  f_inv'' x = - f'' (f_inv x) / (f' (f_inv x)) ^ 3.
Proof.
  intros f f' f'' f_inv f_inv' f_inv'' x H1 H2 H3 H4 H5 H6.
  assert (H7 : forall y, f_inv' y = / (f' (f_inv y))). 
  {
    assert (H7 : ⟦ der ⟧ f_inv = λ y : ℝ, / f' (f_inv y)).
    {
      apply (global_inverse_theorem f f_inv f' H1 H2).
      intro x0.
      intro H7.
      assert (H8 : ⟦ der x0 ⟧ (f_inv ∘ f) = λ y, f_inv' (f y) * f' y) by auto_diff.
      assert (H9 : ⟦ der x0 ⟧ (f_inv ∘ f) = λ _, 1). 
      {
        apply (derivative_at_eq (λ x : ℝ, x) (λ x : ℝ, f_inv (f x)) (λ _ : ℝ, 1) x0); [ | auto_diff ].
        exists 1. split; [ lra |].
        intros x1 _. symmetry. apply inverse_spec, inverse_symmetric; auto.
      }
      pose proof (derivative_at_unique (f_inv ∘ f) (λ y, f_inv' (f y) * f' y) (λ _, 1) x0 H8 H9) as H10.
      unfold compose in H10.
      rewrite H7 in H10.
      lra.
    }
    intros y.
    pose proof derivative_unique f_inv f_inv' (λ y : ℝ, / f' (f_inv y)) H4 H7 as H8.
    rewrite H8. 
    reflexivity.
  }
  assert (H8 : ⟦ der x ⟧ (fun y => f' (f_inv y)) = (fun y => f'' (f_inv y) * f_inv' y)) by auto_diff.
  assert (H9 : ⟦ der x ⟧ (fun y => / (f' (f_inv y))) = (fun y => -1 * (f'' (f_inv y) * f_inv' y) / (f' (f_inv y)) ^ 2)).
  { apply derivative_at_inv; [exact H8 | exact H6]. }
  assert (H10 : ⟦ der x ⟧ f_inv' = (fun y => -1 * (f'' (f_inv y) * f_inv' y) / (f' (f_inv y)) ^ 2)).
  { eapply derivative_at_eq'; [intros y; symmetry; apply H7 | exact H9]. }
  assert (H11 : f_inv'' x = -1 * (f'' (f_inv x) * f_inv' x) / (f' (f_inv x)) ^ 2).
  { apply (derivative_at_unique f_inv' f_inv'' (λ y, -1 * (f'' (f_inv y) * f_inv' y) / f' (f_inv y) ^ 2) x); auto. }
  rewrite H11.
  rewrite H7.
  solve_R.
Qed.