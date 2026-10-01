From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_6_i : ⟦ lim 0 ⟧ (λ x, (1 - x)^^(1/x)) = 1/e.
Proof.
  replace (1/e) with (exp (-1)) by (exact (exp_neg 1)).
  apply limit_eq with (f1 := λ x, exp (log (1 - x) / x)).
  {
    exists 1. split; [lra |].
    intros x H1.
    rewrite Rpower_def_pos; [f_equal; lra | solve_R].
  }
  apply limit_continuous_comp with (L := -1); [ | auto_limit].
  step_lhopital (λ x, -1 / (1 - x)) (λ _ : ℝ, 1).
  auto_limit. simp_zero. apply log_1.
Qed.

Lemma lemma_18_6_ii : ⟦ lim (π/4) ⟧ (λ x, (tan x)^^(tan (2*x))) = 1/e.
Proof.
Abort.

Lemma lemma_18_6_iii : ⟦ lim 0 ⟧ (λ x, cos x^^(1 / x^2)) = 1 / √e.
Proof.
  replace (1 / sqrt e) with (exp (-1 / 2)).
  2: {
    rewrite <- Rpower_sqrt by (unfold e; apply exp_pos).
    rewrite <- exp_Rpower.
    rewrite <- exp_neg. f_equal. lra.
  }
  apply limit_eq with (f1 := λ x, exp (log (cos x) / x^2)).
  {
    exists (1/10). split; [lra |].
    intros x H1.
    rewrite Rpower_def_pos; [f_equal; lra | solve_denoms].
  }
  apply limit_continuous_comp with (L := -1/2); [ | auto_limit].
  step_lhopital (λ x, - sin x / cos x) (λ x, 2 * x).
  step_lhopital (λ x, (- cos x * cos x - (-sin x) * (-sin x)) / cos x^2) (λ _ : ℝ, 2).
Qed.