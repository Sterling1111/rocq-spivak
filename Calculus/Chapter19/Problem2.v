From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_2_i : forall c,
  ∫ (λ x, exp x * sin (exp x)) =
  (λ x, - cos (exp x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_ii : forall c,
  ∫ (λ x, x * exp (- x ^ 2)) =
  (λ x, - 1 / 2 * exp (- x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_iii : forall c,
  ∫ (λ x, log x / x) (0, ∞) =
  (λ x, 1 / 2 * (log x) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_iv : forall c,
  ∫ (λ x, exp x / (exp (2 * x) + 2 * exp x + 1)) =
  (λ x, - 1 / (exp x + 1) + c).
Proof.
  auto_int.
  - pose proof exp_pos x; lra.
  - replace (2 * x) with (x + x) by lra. rewrite theorem_18_3.
    replace (- (-1 * exp x)) with (exp x) by lra. f_equal. lra.
Qed.

Lemma lemma_19_2_v : forall c,
  ∫ (λ x, exp (exp x) * exp x) =
  (λ x, exp (exp x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_vi : forall c,
  ∫ (λ x, x / √ (1 - x ^ 4)) (-1, 1) =
  (λ x, 1 / 2 * arcsin (x ^ 2) + c).
Proof.
  auto_int.
  replace (1 + 1) with 2 by lra.
  replace (1 / 2 * (2 * x / √(1 - x * x * (x * x)))) with ((x / √(1 - x * x * (x * x)))) by lra.
  f_equal. f_equal. lra.
Qed.

Lemma lemma_19_2_vii : forall c,
  ∫ (λ x, exp (√ x) / √ x) (0, ∞) =
  (λ x, 2 * exp (√ x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_2_viii : forall c,
  ∫ (λ x, x * √ (1 - x ^ 2)) (-1, 1) =
  (λ x, - 1 / 3 * ((1 - x ^ 2) ^^ (3 / 2)) + c).
Proof.
  auto_int.
  replace (3 / 2 - 1) with (1 / 2) by lra.
  replace (-1 / 3 * (3 / 2 * (1 - x * x) ^^ (1 / 2) * - ((1 + 1) * x))) with (x * (1 - x * x) ^^ (1 / 2)) by lra.
  rewrite Rpower_sqrt.
  - reflexivity.
  - destruct H; nra.
Qed.

Lemma lemma_19_2_ix : forall c,
  ∫ (λ x, log (cos x) * tan x) (-π / 2, π / 2) =
  (λ x, - 1 / 2 * (log (cos x)) ^ 2 + c).
Proof.
  auto_int.
  unfold tan. lra.
Qed.

Lemma lemma_19_2_x : forall c,
  ∫ (λ x, log (log x) / (x * log x)) (1, ∞) =
  (λ x, 1 / 2 * (log (log x)) ^ 2 + c).
Proof.
  auto_int.
  - pose proof (log_pos x). cbv [Ensembles.In] in H. rewrite ln_eq_log. nra.
Qed.