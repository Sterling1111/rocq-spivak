From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_6_i : ⟦ lim 0 ⟧ (fun x => (1 - x)^^(1/x)) = 1/e.
Proof.
  replace (1/e) with (exp (-1)) by (exact (exp_neg 1)).
  apply limit_eq with (f1 := fun x => exp (log (1 - x) / x)).
  {
    exists 1. split; [lra |].
    intros x H1.
    rewrite Rpower_def_pos; [f_equal; lra | solve_R].
  }
  apply limit_continuous_comp with (L := -1); [ | auto_limit].
  step_lhopital (λ x, -1 / (1 - x)) (λ _ : ℝ, 1).
  auto_limit. simp_zero. apply log_1.
Qed.

Lemma lemma_18_6_ii : ⟦ lim (π/4) ⟧ (fun x => (tan x)^^(tan (2*x))) = 1/e.
Proof.
  replace (1/e) with (exp (-1)) by (exact (exp_neg 1)).
  apply limit_eq with (f1 := fun x => exp ((log (tan x) * sin (2 * x)) / cos (2 * x))).
  {
    exists (1/10). split; [lra |].
    intros x H1.
    rewrite Rpower_def_pos; [| solve_denoms].
    replace (tan (2 * x)) with (sin (2 * x) / cos (2 * x)) by (unfold tan; reflexivity).
    f_equal. field. solve_denoms.
  }
  apply limit_continuous_comp with (L := -1); [ | auto_limit].
  step_lhopital 
    (λ x, ((1 / (cos x)^2) / tan x) * sin (2 * x) + log (tan x) * (cos (2 * x) * 2)) 
    (λ x, - sin (2 * x) * 2).
  - auto_limit; interval.
  - auto_limit. replace (2 * (π / 4)) with (π / 2) by lra. apply cos_π_over_2.
  - exists (1/10); split; auto_diff.
    pose proof sin_gt_0 (2 * x) ltac:(pose proof π_bounds; solve_R). lra.
  - auto_limit; try split; try interval; 
    replace (2 * (π / 4)) with (π / 2) by lra; rewrite sin_π_over_2; try lra.
    simp_zero. rewrite sqrt_def; lra.
Qed.

Lemma lemma_18_6_iii : ⟦ lim 0 ⟧ (λ x, cos x^^(1 / x^2)) = 1 / √e.
Proof.
  replace (1 / sqrt e) with (exp (-1 / 2)).
  2: {
    rewrite <- Rpower_sqrt by (unfold e; apply exp_pos).
    rewrite <- exp_Rpower.
    rewrite <- exp_neg. f_equal. lra.
  }
  apply limit_eq with (f1 := fun x => exp (log (cos x) / x^2)).
  {
    exists (1/10). split; [lra |].
    intros x H1.
    rewrite Rpower_def_pos; [f_equal; lra | solve_denoms].
  }
  apply limit_continuous_comp with (L := -1/2); [ | auto_limit].
  step_lhopital (λ x, - sin x / cos x) (λ x, 2 * x).
  step_lhopital (λ x, (- cos x * cos x - (-sin x) * (-sin x)) / cos x^2) (λ _ : ℝ, 2).
Qed.