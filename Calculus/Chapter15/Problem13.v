From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_13_a_cos : ∀ (f : ℝ → ℝ) (n : ℕ),
  (n > 0)%nat ->
  integrable_on (-π) π f ->
  ∀ a, ∫ (-π) π (λ x, (f x - a * cos (n * x))^2) >=
            ∫ (-π) π (λ x, (f x - (1/π * ∫ (-π) π (λ t, f t * cos (n * t))) * cos (n * x))^2).
Proof.
  intros f n H0 H1 a.
  set (H := λ a, ∫ (- π) π (λ x, (f x - a * cos (n * x)) ^ 2)).
  replace (∫ (- π) π (λ x : ℝ, (f x - a * cos (n * x)) ^ 2)) with (H a) by reflexivity.
  assert (H2 : ⟦ der ⟧ H = (λ a, 2 * a * ∫ (-π) π (λ x, (cos (n * x))^2) - 2 * ∫ (-π) π (λ x, f x * cos (n * x)))).
  {
    unfold H.
    replace (λ a, ∫ (- π) π (λ x : ℝ, (f x - a * cos (n * x)) ^ 2)) with 
            (λ a, a^2 * ∫ (-π) π (λ x, (cos (n * x))^2) - 2 * a * ∫ (-π) π (λ x, f x * cos (n * x)) + ∫ (-π) π (λ x, (f x)^2)).
    2 : {
      extensionality x.
      replace (λ x0 : ℝ, (f x0 - x * cos (n * x0)) ^ 2) with 
              (λ x0 : ℝ, x^2 * (cos (n * x0))^2 - 2 * x * f x0 * cos (n * x0) + (f x0)^2) by (extensionality y; lra).
      assert (-π < π) by solve_denoms.
      rewrite integral_plus; auto; try lra. rewrite integral_minus; auto; try lra.
      2 : { apply theorem_13_3; auto_cont. }
      2 : { apply integrable_mult; auto; try solve_R. apply integrable_mult; auto; try solve_R. all : apply theorem_13_3; auto_cont. }
      2 : { apply integrable_minus; auto; try solve_R.
       apply theorem_13_3; auto_cont. apply integrable_mult; auto; try solve_R.
       apply integrable_mult; auto; try solve_R. all : apply theorem_13_3; auto_cont.
      }
      2 : { apply integrable_mult; auto; try solve_R. apply integrable_mult; auto; try solve_R. apply theorem_13_3; auto_cont. }
      replace (λ x0 : ℝ, 2 * x * f x0 * cos (n * x0)) with  (λ x0 : ℝ, (2 * x) * (f x0 * cos (n * x0))) by (extensionality y; lra).
      repeat rewrite integral_mult_scalar; auto; try solve_R.
      apply integrable_mult; auto; try solve_R. all : apply theorem_13_3; auto_cont.
    }
    auto_diff.
  }
  assert (H3 : minimum_point H ℝ (1 / π * ∫ (- π) π (λ t : ℝ, f t * cos (n * t)))).
  {
    apply first_derivative_test_min with (f' := λ a : ℝ, 2 * a * ∫ (- π) π (λ x : ℝ, cos (n * x) ^ 2) - 2 * ∫ (- π) π (λ x : ℝ, f x * cos (n * x))); auto; try solve_R.
    - intros x H3.
      rewrite Integral_Table.integral_113; auto; try solve_R.
      pose proof π_pos.
      replace (2 * ∫ (- π) π (λ x0 : ℝ, f x0 * cos (n * x0))) with (2 * π * (1 / π * ∫ (- π) π (λ t : ℝ, f t * cos (n * t)))) by (field; lra).
      nra.
    - intros x H3.
      rewrite Integral_Table.integral_113; auto; try solve_R.
      pose proof π_pos.
      replace (2 * ∫ (- π) π (λ x0 : ℝ, f x0 * cos (n * x0))) with (2 * π * (1 / π * ∫ (- π) π (λ t : ℝ, f t * cos (n * t)))) by (field; lra).
      nra.
  }
  destruct H3 as [_ H3].
  specialize (H3 a (Full_intro ℝ a)).
  unfold H in *; lra.
Qed.

Lemma lemma_15_13_a_sin : ∀ (f : ℝ → ℝ) (n : ℕ),
  (n > 0)%nat ->
  integrable_on (-π) π f ->
  ∀ a, ∫ (-π) π (λ x, (f x - a * sin (n * x))^2) >=
            ∫ (-π) π (λ x, (f x - (1/π * ∫ (-π) π (λ t, f t * sin (n * t))) * sin (n * x))^2).
Proof.
Abort.