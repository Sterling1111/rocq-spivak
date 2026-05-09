From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_10 : ∀ f h k,
  (∀ x, x ≠ 0 -> f x = x^2 * sin (1 / x)) ->
  f 0 = 0 ->
  ⟦ der ⟧ h = (λ x, sin (sin (x + 1))^2) ->
  h 0 = 3 ->
  ⟦ der ⟧ k = (λ x, f (x + 1)) ->
  k 0 = 0 ->
  ∀ α, α = (λ x, h (x^2)) ->
  (⟦ der 0 ⟧ (f ∘ h) = λ _, (6 * sin (1 / 3) - cos (1 / 3)) * sin (sin 1)^2) /\
  (⟦ der 0 ⟧ (k ∘ f) = λ _, 0) /\
  (⟦ der ⟧ α = λ x, 2 * x * sin (sin (x^2 + 1))^2).
Proof.
  intros f h k H1 H2 H3 H4 H5 H6 α H7.
  assert (H8 : continuous_at h 0).
  { apply differentiable_imp_continuous. eapply derivative_imp_differentiable; eauto. }
  repeat split.
  - apply derivative_at_eq with (f1 := fun x => h x ^ 2 * sin (1 / h x)).
    + specialize (H8 (3/2) ltac:(lra)) as [δ [H9 H10]]. exists δ. split; auto.
      intros x H11. unfold compose. rewrite H1. reflexivity.
      assert (x = 0 \/ x <> 0) as [H12 | H12] by lra.
      * subst. lra.
      * intros H13. specialize (H10 x ltac:(solve_R)). rewrite H4, H13 in *. solve_R. 
    + auto_diff. rewrite H4. lra.
  - assert (H9 : ⟦ der 0 ⟧ f = λ _, 0).
    {
      apply limit_eq with (f1 := fun h => h * sin (1 / h)).
      - exists 1. split; [lra |].
        intros x H9. simp_zero. rewrite H1, H2; solve_R.
      - apply limit_squeeze with (a := -1) (b := 1) (f1 := fun x => - Rabs x) (f3 := fun x => Rabs x); try auto_limit.
        intros x H9.
        pose proof (sin_bounds (1 / x)) as [H11 H12]. solve_R.
    }
    assert (H10 : ⟦ der f 0 ⟧ k = λ x : ℝ, f (x + 1)).
    { rewrite H2. apply H5. }
    replace (λ _ : ℝ, 0) with (((λ x0 : ℝ, f (x0 + 1)%R) ∘ f)%function ⋅ λ _ : ℝ, 0) by (extensionality x; lra).
    apply derivative_at_comp; auto_diff.
  - subst α. auto_diff.
Qed.