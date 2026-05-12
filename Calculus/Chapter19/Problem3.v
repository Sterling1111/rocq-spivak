From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_3_i : forall c,
  ∫ (λ x, x ^ 2 * exp x) =
  (λ x, exp x * (x ^ 2 - 2 * x + 2) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_3_ii : forall c,
  ∫ (λ x, x ^ 3 * exp (x ^ 2)) =
  (λ x, 1 / 2 * exp (x ^ 2) * (x ^ 2 - 1) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_3_iii : forall a b c, a ^ 2 + b ^ 2 <> 0 ->
  ∫ (λ x, exp (a * x) * sin (b * x)) =
  (λ x, exp (a * x) * (a * sin (b * x) - b * cos (b * x)) / (a ^ 2 + b ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_3_iv : forall c,
  ∫ (λ x, x ^ 2 * sin x) =
  (λ x, - x ^ 2 * cos x + 2 * x * sin x + 2 * cos x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_3_v : forall c,
  ∫ (λ x, (log x) ^ 3) (0, ∞) =
  (λ x, x * (log x) ^ 3 - 3 * x * (log x) ^ 2 + 6 * x * log x - 6 * x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_3_vi : forall c,
  ∫ (λ x, log (log x) / x) (1, ∞) =
  (λ x, log x * log (log x) - log x + c).
Proof.
  auto_int.
  pose proof (log_pos x). rewrite ln_eq_log. solve_R.
Qed.

Lemma lemma_19_3_vii : forall c,
  ∫ (λ x, 1 / (cos x) ^ 3) (-π / 2, π / 2) =
  (λ x, 1 / 2 * (sin x / (cos x) ^ 2 + log ((1 + sin x) / cos x)) + c).
Proof.
  auto_int.
  - pose proof cos_gt_0 x; solve_R.
  - apply Rdiv_pos_pos.
    + admit.
    + apply cos_gt_0; solve_R.
  - admit.
Admitted.

Lemma lemma_19_3_viii : forall c,
  ∫ (λ x, cos (log x)) (0, ∞) =
  (λ x, 1 / 2 * x * (cos (log x) + sin (log x)) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_3_ix : forall c,
  ∫ (λ x, √ x * log x) (0, ∞) =
  (λ x, 2 / 3 * (x ^^ (3 / 2)) * log x - 4 / 9 * (x ^^ (3 / 2)) + c).
Proof.
  auto_int.
  solve_R.
  replace (3/2 - 1) with (1/2) by lra.
  rewrite Rpower_sqrt by lra.
  replace (x^^(3/2)) with (x * √x).
  2 : {
    replace (3/2) with (1/2 + 1) by lra.
    rewrite Rpower_plus, Rpower_1, Rpower_sqrt; lra.
  }
  lra.
Qed.

Lemma lemma_19_3_x : forall c,
  ∫ (λ x, x * (log x) ^ 2) (0, ∞) =
  (λ x, 1 / 2 * x ^ 2 * (log x) ^ 2 - 1 / 2 * x ^ 2 * log x + 1 / 4 * x ^ 2 + c).
Proof.
  auto_int.
Qed.