From Calculus.Chapter15 Require Import Prelude.
From Calculus.Chapter15 Require Import Problem11.

Lemma lemma_15_12_a : ∀ (m n : nat),
  m <> n ->
  ∫ (-π) π (λ x, sin (m * x) * sin (n * x)) = 0.
Proof.
  intros m n H1.
  replace (λ x, sin (m * x) * sin (n * x)) with (λ x, (cos ((m - n) * x) - cos ((m + n) * x)) / 2).
  2 : { extensionality x. rewrite lemma_15_11_a. lra. }
  assert (H2 : - π < π). { pose proof π_pos; lra. }
  set (g := λ x, (sin ((m - n) * x) / (m - n) - sin ((m + n) * x) / (m + n)) / 2).
  assert (H3 : continuous_on (λ x, (cos ((m - n) * x) - cos ((m + n) * x)) / 2) [- π, π]) by auto_cont.
  assert (H4 : ⟦ der ⟧ g [- π, π] = (λ x, (cos ((m - n) * x) - cos ((m + n) * x)) / 2)).
  {
    unfold g; auto_diff; solve_R; intros H4; apply H1; apply INR_eq; solve_R;
    pose proof (pos_INR m); pose proof (pos_INR n); lra.
  }
  rewrite FTC2 with (g := g); auto.
  unfold g.
  assert (H5 : sin ((m - n) * π) = 0).
  { apply sin_eq_0. exists (Z.of_nat m - Z.of_nat n)%Z. rewrite <- Z_R_minus. rewrite <- !INR_IZR_INZ. reflexivity. }
  assert (H6 : sin ((m + n) * π) = 0).
  { apply sin_eq_0. exists (Z.of_nat m + Z.of_nat n)%Z. rewrite plus_IZR. rewrite <- !INR_IZR_INZ. reflexivity. }
  assert (H7 : sin ((m - n) * - π) = 0).
  { replace ((m - n) * - π) with (- ((m - n) * π)) by lra. rewrite sin_even_odd. rewrite H5. lra. }
  assert (H8 : sin ((m + n) * - π) = 0).
  { replace ((m + n) * - π) with (- ((m + n) * π)) by lra. rewrite sin_even_odd. rewrite H6. lra. }
  rewrite H5, H6, H7, H8.
  lra.
Qed.

Lemma lemma_15_12_a' : ∀ (n : nat),
  (n > 0)%nat ->
  ∫ (-π) π (λ x, sin (n * x) * sin (n * x)) = π.
Proof.
  intros n H1.
  replace (λ x, sin (n * x) * sin (n * x)) with (λ x, (1 - cos ((n + n) * x)) / 2).
  2 : { extensionality x. rewrite lemma_15_11_a. replace ((n - n) * x) with 0 by solve_R. rewrite cos_0. lra. }
  assert (H2 : - π < π). { pose proof π_pos; lra. }
  set (g := λ x, (x - sin ((n + n) * x) / (n + n)) / 2).
  assert (H3 : continuous_on (λ x, (1 - cos ((n + n) * x)) / 2) [- π, π]) by auto_cont.
  assert (H4 : ⟦ der ⟧ g [- π, π] = (λ x, (1 - cos ((n + n) * x)) / 2)).
  { unfold g; auto_diff; solve_R. }
  rewrite FTC2 with (g := g); auto.
  unfold g.
  assert (H5 : sin ((n + n) * π) = 0).
  { apply sin_eq_0. exists (Z.of_nat n + Z.of_nat n)%Z. rewrite plus_IZR. rewrite <- !INR_IZR_INZ. reflexivity. }
  assert (H6 : sin ((n + n) * - π) = 0).
  { replace ((n + n) * - π) with (- ((n + n) * π)) by lra. rewrite sin_even_odd. rewrite H5. lra. }
  rewrite H5, H6.
  lra.
Qed.

Lemma lemma_15_12_b : ∀ (m n : nat),
  m <> n ->
  ∫ (-π) π (λ x, cos (m * x) * cos (n * x)) = 0.
Proof.
  intros m n H1.
  replace (λ x, cos (m * x) * cos (n * x)) with (λ x, (cos ((m + n) * x) + cos ((m - n) * x)) / 2).
  2 : { extensionality x. rewrite lemma_15_11_c. lra. }
  assert (H2 : - π < π). { pose proof π_pos; lra. }
  set (g := λ x, (sin ((m + n) * x) / (m + n) + sin ((m - n) * x) / (m - n)) / 2).
  assert (H3 : continuous_on (λ x, (cos ((m + n) * x) + cos ((m - n) * x)) / 2) [- π, π]) by auto_cont.
  assert (H4 : ⟦ der ⟧ g [- π, π] = (λ x, (cos ((m + n) * x) + cos ((m - n) * x)) / 2)).
  {
    unfold g; auto_diff; solve_R; intros H4; apply H1; apply INR_eq; solve_R;
    pose proof (pos_INR m); pose proof (pos_INR n); lra.
  }
  rewrite FTC2 with (g := g); auto.
  unfold g.
  assert (H5 : sin ((m - n) * π) = 0).
  { apply sin_eq_0. exists (Z.of_nat m - Z.of_nat n)%Z. rewrite <- Z_R_minus. rewrite <- !INR_IZR_INZ. reflexivity. }
  assert (H6 : sin ((m + n) * π) = 0).
  { apply sin_eq_0. exists (Z.of_nat m + Z.of_nat n)%Z. rewrite plus_IZR. rewrite <- !INR_IZR_INZ. reflexivity. }
  assert (H7 : sin ((m - n) * - π) = 0).
  { replace ((m - n) * - π) with (- ((m - n) * π)) by lra. rewrite sin_even_odd. rewrite H5. lra. }
  assert (H8 : sin ((m + n) * - π) = 0).
  { replace ((m + n) * - π) with (- ((m + n) * π)) by lra. rewrite sin_even_odd. rewrite H6. lra. }
  rewrite H5, H6, H7, H8.
  lra.
Qed.

Lemma lemma_15_12_b' : ∀ (n : nat),
  (n > 0)%nat ->
  ∫ (-π) π (λ x, cos (n * x) * cos (n * x)) = π.
Proof.
  intros n H1.
  replace (λ x, cos (n * x) * cos (n * x)) with (λ x, (1 + cos ((n + n) * x)) / 2).
  2 : { extensionality x. rewrite lemma_15_11_c. replace ((n - n) * x) with 0 by solve_R. rewrite cos_0. lra. }
  assert (H2 : - π < π). { pose proof π_pos; lra. }
  set (g := λ x, (x + sin ((n + n) * x) / (n + n)) / 2).
  assert (H3 : continuous_on (λ x, (1 + cos ((n + n) * x)) / 2) [- π, π]) by auto_cont.
  assert (H4 : ⟦ der ⟧ g [- π, π] = (λ x, (1 + cos ((n + n) * x)) / 2)).
  { unfold g; auto_diff; solve_R. }
  rewrite FTC2 with (g := g); auto.
  unfold g.
  assert (H5 : sin ((n + n) * π) = 0).
  { apply sin_eq_0. exists (Z.of_nat n + Z.of_nat n)%Z. rewrite plus_IZR. rewrite <- !INR_IZR_INZ. reflexivity. }
  assert (H6 : sin ((n + n) * - π) = 0).
  { replace ((n + n) * - π) with (- ((n + n) * π)) by lra. rewrite sin_even_odd. rewrite H5. lra. }
  rewrite H5, H6.
  lra.
Qed.

Lemma lemma_15_12_c : ∀ (m n : nat),
  ∫ (-π) π (λ x, sin (m * x) * cos (n * x)) = 0.
Proof.
  intros m n.
  replace (λ x, sin (m * x) * cos (n * x)) with (λ x, (sin ((m + n) * x) + sin ((m - n) * x)) / 2).
  2 : { extensionality x. rewrite lemma_15_11_b. lra. }
  assert (H2 : - π < π). { pose proof π_pos; lra. }
  set (g := λ x, (- cos ((m + n) * x) / (m + n) - cos ((m - n) * x) / (m - n)) / 2).
  assert (H3 : continuous_on (λ x : ℝ, (sin ((m + n) * x) + sin ((m - n) * x)) / 2) [- π, π]) by auto_cont.
  assert (H4 : ⟦ der ⟧ g [- π, π] = λ x : ℝ, (sin ((m + n) * x) + sin ((m - n) * x)) / 2).
  {
    assert (m < n \/ m > n \/ m = n)%nat as [H4 | [H4 | H4]] by lia.
    - unfold g; auto_diff; pose proof (pos_INR m); pose proof (pos_INR n); solve_R.
    - unfold g; auto_diff; pose proof (pos_INR m); pose proof (pos_INR n); solve_R.
    - assert (m = 0 \/ m > 0)%nat as [H5 | H5] by lia.
      + unfold g.
        replace ((λ x : ℝ, (- cos ((m + n) * x) / (m + n) - cos ((m - n) * x) / (m - n)) / 2)) with
                (λ x : ℝ, 0).
        2 : { extensionality x. subst. simpl. simp_zero. rewrite <- Ropp_mult_distr_l. simp_zero. rewrite Ropp_0, 2 Rdiv_0_r. lra. }
        replace (λ x : ℝ, (sin ((m + n) * x) + sin ((m - n) * x)) / 2) with (λ _ : ℝ, 0).
        2 : { extensionality x. subst. simpl. simp_zero. rewrite <- Ropp_mult_distr_l. simp_zero. rewrite Ropp_0, sin_0. lra. }
        auto_diff.
      + unfold g.
        replace ((λ x : ℝ, (- cos ((m + n) * x) / (m + n) - cos ((m - n) * x) / (m - n)) / 2)) with 
                ((λ x : ℝ, (- cos ((m + n) * x) / (m + n)) / 2)).
        2 : { extensionality x. subst. rewrite Rminus_diag. simp_zero. rewrite Rdiv_0_r. lra. }
        replace (λ x : ℝ, (sin ((m + n) * x) + sin ((m - n) * x)) / 2) with (λ x : ℝ, (sin ((m + n) * x) / 2)).
        2 : { extensionality x. subst. rewrite Rminus_diag. simp_zero. rewrite sin_0. lra. }
        auto_diff; pose proof (pos_INR m); pose proof (pos_INR n); solve_R.
  }
  rewrite FTC2 with (g := g); auto.
  unfold g.
  assert (H5 : cos ((m - n) * π) = cos ((m - n) * - π)).
  { replace ((m - n) * - π) with (- ((m - n) * π)) by lra. rewrite cos_even_odd. reflexivity. }
  assert (H6 : cos ((m + n) * π) = cos ((m + n) * - π)).
  { replace ((m + n) * - π) with (- ((m + n) * π)) by lra. rewrite cos_even_odd. reflexivity. }
  rewrite H5, H6.
  lra.
Qed.
