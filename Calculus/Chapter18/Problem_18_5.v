From Calculus.Chapter18 Require Import Prelude.

Ltac step_lhopital f_prime g_prime :=
  apply lhopital_0_0 with (f' := f_prime) (g' := g_prime);
  try solve [auto_limit];
  try solve [auto_diff];
  try (exists 1; split; try lra; auto_diff).

Lemma lemma_18_5_i : ⟦ lim 0 ⟧ (fun x => (exp x - 1 - x - x^2 / 2) / x^2) = 0.
Proof.
  step_lhopital (λ x, (exp x)-1-x) (λ x, 2*x).
  step_lhopital (λ x, (exp x)-1) (λ x : R, 2).
Qed.

Lemma lemma_18_5_ii : ⟦ lim 0 ⟧ (fun x => (exp x - 1 - x - x^2 / 2 - x^3 / 6) / x^3) = 0.
Proof.
  step_lhopital (λ x, (exp x)-1-x-x^2/2) (λ x, 3*x^2).
  step_lhopital (λ x, (exp x)-1-x) (λ x, 6*x).
  step_lhopital (λ x, (exp x)-1) (λ x : R, 6).
Qed.

Lemma lemma_18_5_iii : ⟦ lim 0 ⟧ (fun x => (exp x - 1 - x - x^2 / 2) / x^3) = 1/6.
Proof.
  step_lhopital (λ x, (exp x)-1-x) (λ x, 3*x^2).
  step_lhopital (λ x, (exp x)-1) (λ x, 6*x).
  step_lhopital (λ x, exp x) (λ x : R, 6).
Qed.

Lemma lemma_18_5_iv : ⟦ lim 0 ⟧ (fun x => (ln (1 + x) - x + x^2 / 2) / x^2) = 0.
Proof.
  step_lhopital (λ x, 1 / (1 + x) - 1 + x) (λ x, 2 * x).
  auto_limit. rewrite Rplus_0_r, log_1. lra.
  step_lhopital (λ x, -1 / (1 + x)^2 + 1) (λ x : R, 2).
Qed.

Lemma lemma_18_5_v : ⟦ lim 0 ⟧ (fun x => (ln (1 + x) - x + x^2 / 2) / x^3) = 1/3.
Proof.
  step_lhopital (λ x, 1 / (1 + x) - 1 + x) (λ x, 3 * x^2).
  auto_limit. rewrite Rplus_0_r, log_1. lra.
  step_lhopital (λ x, -1 / (1 + x)^2 + 1) (λ x, 6 * x).
  step_lhopital (λ x, 2 / (1 + x)^3) (λ x : R, 6).
Qed.

Lemma lemma_18_5_vi : ⟦ lim 0 ⟧ (fun x => (ln (1 + x) - x + x^2 / 2 - x^3 / 3) / x^3) = 0.
Proof.
  step_lhopital (λ x, 1 / (1 + x) - 1 + x - x^2) (λ x, 3 * x^2).
  auto_limit. rewrite Rplus_0_r, log_1. lra.
  step_lhopital (λ x, -1 / (1 + x)^2 + 1 - 2 * x) (λ x, 6 * x).
  step_lhopital (λ x, 2 / (1 + x)^3 - 2) (λ x : R, 6).
Qed.