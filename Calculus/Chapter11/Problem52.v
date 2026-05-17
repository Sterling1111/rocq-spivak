From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_52_i : ⟦ lim 0 ⟧ (λ x, x / tan x) = 1.
Proof.
  step_lhopital (λ x : ℝ, 1) (λ x, 1 / (cos x)^2).
  exists (π / 2). split; [ pose proof π_pos; lra |].
  intros x H1 H2.
  pose proof cos_gt_0 x ltac:(solve_R) as H3.
  apply Rgt_not_eq, Rmult_gt_reg_r with (r := cos x ^ 2); 
  field_simplify; nra.
Qed.

Lemma lemma_11_52_ii : ⟦ lim 0 ⟧ (λ x, ((cos x)^2 - 1) / x^2) = -1.
Proof.
  step_lhopital (λ x, -2 * cos x * sin x) (λ x, 2 * x).
  step_lhopital (λ x, 2 * (sin x)^2 - 2 * (cos x)^2) (λ x : ℝ, 2).
Qed.