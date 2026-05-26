From Calculus.Chapter10 Require Import Prelude.

Section section_10_10.

  Variables f h k α : ℝ -> ℝ.

  Hypothesis H1 : ∀ x, x <> 0 -> f x = x^2 * sin (1 / x).
  Hypothesis H2 : f 0 = 0.
  Hypothesis H3 : h 0 = 3.
  Hypothesis H4 : k 0 = 0.
  Hypothesis H5 : ⟦ der ⟧ h = (λ x, sin (sin (x + 1))^2).
  Hypothesis H6 : ⟦ der ⟧ k = (λ x, f (x + 1)).
  Hypothesis H7 : α = λ x, h (x^2).

  Lemma lemma_10_10_i : ⟦ der 0 ⟧ (f ∘ h) = λ _, (6 * sin (1 / 3) - cos (1 / 3)) * sin (sin 1)^2.
  Proof.
    assert (H8 : continuous_at h 0).
    { apply differentiable_imp_continuous. eapply derivative_imp_differentiable; eauto. }
    apply derivative_at_eq with (f1 := fun x => h x ^ 2 * sin (1 / h x)).
    - specialize (H8 (3/2) ltac:(lra)) as [δ [H9 H10]]. exists δ. split; auto.
      intros x H11. unfold compose. rewrite H1. reflexivity.
      assert (x = 0 \/ x <> 0) as [H12 | H12] by lra.
      + subst. lra.
      + intros H13. specialize (H10 x ltac:(solve_R)). rewrite H3, H13 in *. solve_R. 
    - auto_diff. rewrite H3. lra.
  Qed.

  Lemma lemma_10_10_ii : ⟦ der 0 ⟧ (k ∘ f) = λ _, 0.
  Proof.
    assert (H8 : ⟦ der 0 ⟧ f = λ _, 0).
    { apply limit_eq with (f1 := fun h0 => h0 * sin (1 / h0)).
      - exists 1. split; [lra |].
        intros x H8. simp_zero. rewrite H1, H2; solve_R.
      - apply limit_squeeze with (a := -1) (b := 1) (f1 := fun x => - Rabs x) (f3 := fun x => Rabs x); try auto_limit.
        intros x H8. pose proof (sin_bounds (1 / x)) as [H9 H10]. solve_R. }
    assert (H9 : ⟦ der f 0 ⟧ k = λ x : ℝ, f (x + 1)).
    { rewrite H2. apply H6. }
    replace (λ _ : ℝ, 0) with (((λ x0 : ℝ, f (x0 + 1)%R) ∘ f)%function ⋅ λ _ : ℝ, 0) by (extensionality x; lra).
    apply derivative_at_comp; auto_diff.
  Qed.

  Lemma lemma_10_10_iii : ∀ x α',
    ⟦ der ⟧ α = α' -> α' (x^2) = 2 * (x^2) * sin (sin (x^4 + 1))^2.
  Proof.
    intros x α' H8.
    assert (H9 : ⟦ der ⟧ α = λ x, 2 * x * sin (sin (x^2 + 1))^2) by (subst; auto_diff).
    rewrite (derivative_at_unique α α' (λ x : ℝ, 2 * x * sin (sin (x ^ 2 + 1)) ^ 2)); auto.
    replace ((x^2)^2) with (x^4) by lra.
    reflexivity.
  Qed.

  Lemma lemma_10_10_iii' : ⟦ der ⟧ α = λ x, 2 * x * sin (sin (x^2 + 1))^2.
  Proof. subst α. auto_diff. Qed.

End section_10_10.
      
    
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