From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_1_i : forall c,
  ∫ (λ x, ((x ^^ (3 / 5)) + (x ^^ (1 / 6))) / √ x) (0, ∞) =
  (λ x, 10 / 11 * (x ^^ (11 / 10)) + 3 / 2 * (x ^^ (2 / 3)) + c).
Proof.
  intros c. unfold antiderivative_on. auto_diff. field_simplify.
  - replace (11 / 10 - 1) with (1 / 10) by lra.
    replace (2 / 3 - 1) with (-1 / 3) by lra.
    rewrite <- Rpower_sqrt; auto.
    replace ((x ^^ (3 / 5) + x ^^ (1 / 6)) / x ^^ (1 / 2)) with (x ^^ (3 / 5) / x ^^ (1 / 2) + x ^^ (1 / 6) / x ^^ (1 / 2)) by lra.
    repeat rewrite <- Rpower_minus; auto.
    replace (3 / 5 - 1 / 2) with (1 / 10) by lra.
    replace (1 / 6 - 1 / 2) with (-1 / 3) by lra.
    reflexivity.
  - pose proof sqrt_lt_R0 x ltac:(solve_R). lra.
Qed.
    
Lemma lemma_19_1_ii : forall c,
  ∫ (λ x, 1 / (√ (x - 1) + √ (x + 1))) (1, ∞) =
  (λ x, 1 / 3 * ((x + 1) ^^ (3 / 2)) - 1 / 3 * ((x - 1) ^^ (3 / 2)) + c).
Proof.
  intros c. unfold antiderivative_on. auto_diff.
  replace (3 / 2 - 1) with (1 / 2) by lra.
  pose proof (Rpower_gt_0 (x - 1) (1 / 2) ltac:(solve_R)) as H1.
  pose proof (Rpower_gt_0 (x + 1) (1 / 2) ltac:(solve_R)) as H2.
  repeat rewrite <- Rpower_sqrt; auto; try solve_R.
  replace (0 * (x + 1) ^^ (3 / 2) + 1 / 3 * (3 / 2 * (x + 1) ^^ (1 / 2) * (1 + 0)) - (0 * (x - 1) ^^ (3 / 2) + 1 / 3 * (3 / 2 * (x - 1) ^^ (1 / 2) * (1 - 0))) + 0) with (1 / 2 * (x + 1) ^^ (1 / 2) - 1 / 2 * (x - 1) ^^ (1 / 2)) by lra.
  assert (H3: (x+1)^^(1/2) * (x+1)^^(1/2) = x+1).
  { rewrite <- Rpower_plus; try solve_R; replace (1/2 + 1/2) with 1 by lra; rewrite Rpower_1; try solve_R; reflexivity. }
  assert (H4: (x-1)^^(1/2) * (x-1)^^(1/2) = x-1).
  { rewrite <- Rpower_plus; try solve_R; replace (1/2 + 1/2) with 1 by lra; rewrite Rpower_1; try solve_R; reflexivity. }
  assert (H5: (x - 1)^^(1 / 2) + (x + 1)^^(1 / 2) <> 0).
  { pose proof Rpower_gt_0 (x-1) (1/2) ltac:(solve_R). pose proof Rpower_gt_0 (x+1) (1/2) ltac:(solve_R). lra. }
  apply Rmult_eq_reg_r with (r := ((x - 1)^^(1 / 2) + (x + 1)^^(1 / 2))); auto.
  replace (1 / ((x - 1)^^(1 / 2) + (x + 1)^^(1 / 2)) * ((x - 1)^^(1 / 2) + (x + 1)^^(1 / 2))) with 1 by (field; auto).
  nra.
Qed.

Lemma lemma_19_1_iii : forall c,
  ∫ (λ x, (exp x + exp (2 * x) + exp (3 * x)) / exp (4 * x)) =
  (λ x, -1 / 3 * exp (-3 * x) - 1 / 2 * exp (-2 * x) - exp (-x) + c).
Proof.
  intros c. unfold antiderivative. auto_diff. field_simplify.
  - replace ((6 * exp (-3 * x) + 6 * exp (-2 * x) + 6 * exp (- x)) / 6) with (exp (-3 * x) + exp (-2 * x) + exp (- x)) by lra.
    replace (exp (-3 * x) + exp (-2 * x) + exp (- x)) with ((exp (-3 * x) * exp (4 * x) + exp (-2 * x) * exp (4 * x) + exp (- x) * exp (4 * x)) / exp (4 * x)).
    + f_equal. repeat rewrite <- theorem_18_3.
      replace (-3 * x + 4 * x) with x by lra.
      replace (-2 * x + 4 * x) with (2 * x) by lra.
      replace (- x + 4 * x) with (3 * x) by lra.
      reflexivity.
    + field. apply exp_neq_0.
  - apply exp_neq_0.
Qed.

Lemma lemma_19_1_iv : forall a b c, a > 0 -> b > 0 -> a <> b ->
  ∫ (λ x, (a ^^ x) / (b ^^ x)) =
  (λ x, ((a / b) ^^ x) / log (a / b) + c).
Proof.
  intros a b c H1 H2 H3. unfold antiderivative. auto_diff.
  - apply Rdiv_pos_pos; lra.
  - apply log_div_neq_0; auto.
  - pose proof Rpower_gt_0 b x H2 as H4. pose proof log_div_neq_0 a b H1 H2 H3 as H5.
    rewrite Rpower_div; solve_R. repeat split; solve_R. rewrite ln_eq_log; auto.
Qed.

Lemma lemma_19_1_v : forall c,
  ∫ (λ x, (tan x) ^ 2) (-π / 2, π / 2) = 
  (λ x, tan x - x + c).
Proof.
  intros c. unfold antiderivative_on. pose proof π_bounds as H1.
  assert (H2 : forall x, x ∈ (- π / 2, π / 2) -> cos x <> 0).
  {
    intros x H2.
    assert (x = 0 \/ 0 < x < π / 2 \/ - (π / 2) < x < 0) as [H3 | [H3 | H3]] by solve_R.
    - subst. rewrite cos_0. lra.
    - pose proof (cos_gt_0_on_open_pi_2 x H3). lra.
    - pose proof (cos_gt_0_on_open_pi_2 (-x) ltac:(solve_R)) as H4.
      rewrite cos_even_odd in H4. lra.
  }
  auto_diff.
  unfold tan.
  pose proof pythagorean_identity x as H3.
  solve_R.
Qed.

Lemma lemma_19_1_vi : forall a c, a <> 0 ->
  ∫ (λ x, 1 / (a ^ 2 + x ^ 2)) =
  (λ x, 1 / a * arctan (x / a) + c).
Proof.
  intros a c H1. unfold antiderivative. auto_diff.
Qed.

Lemma lemma_19_1_vii : forall a c, a > 0 ->
  ∫ (λ x, 1 / √ (a ^ 2 - x ^ 2)) (-a, a) = 
  (λ x, arcsin (x / a) + c).
Proof.
  intros a c H1. unfold antiderivative_on. auto_diff.
  - apply Rmult_lt_reg_r with (r:=a); field_simplify; solve_R.
  - apply Rmult_lt_reg_r with (r:=a); field_simplify; solve_R.
  - admit.
Abort.

Lemma lemma_19_1_viii : forall c,
  ∫ (λ x, 1 / (1 + sin x)) (-π / 2, π / 2) = 
  (λ x, tan x - 1 / cos x + c).
Proof.
  auto_int.
  assert (H1 : ∀ x, x ∈ (- π / 2, π / 2) → cos x ≠ 0).
  {
    intros y H2. apply Rgt_not_eq. unfold Ensembles.In in H2.
    assert (0 < y \/ y = 0 \/ y < 0) as [H3 | [H3 | H3]] by lra.
    - apply cos_gt_0_on_open_pi_2; lra.
    - subst y. rewrite cos_0. lra.
    - rewrite <- cos_even_odd. apply cos_gt_0_on_open_pi_2; lra.
  }
  specialize (H1 x H).
  pose proof pythagorean_identity x. solve_R.
Qed.

Lemma lemma_19_1_ix : forall c,
  ∫ (λ x, (8 * x ^ 2 + 6 * x + 4) / (x + 1)) (-0.5, 0.5) =
  (λ x, 4 * x ^ 2 - 2 * x + 6 * log (x + 1) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_1_x : forall c,
  ∫ (λ x, 1 / √ (2 * x - x ^ 2)) (0, 2) = 
  (λ x, arcsin (x - 1) + c).
Proof.
  auto_int.
Abort.