From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_8_i : forall c,
  ∫ (λ x, arctan x / (1 + x ^ 2)) =
  (λ x, 1 / 2 * (arctan x) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_8_ii : forall c,
  ∫ (λ x, x * arctan x / ((1 + x ^ 2) ^ 2)) =
  (λ x, (x ^ 2 - 1) * arctan x / (4 * (1 + x ^ 2)) + x / (4 * (1 + x ^ 2)) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_8_iii : forall c,
  ∫ (λ x, log (√ (1 + x ^ 2))) =
  (λ x, x * log (√ (1 + x ^ 2)) - x + arctan x + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_iv : forall c,
  ∫ (λ x, x * log (√ (1 + x ^ 2))) =
  (λ x, 1 / 4 * (1 + x ^ 2) * log (1 + x ^ 2) - 1 / 4 * x ^ 2 + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_v : forall c,
  ∫ (λ x, (x ^ 2 - 1) / (x ^ 2 + 1) * (1 / √ (1 + x ^ 4))) =
  (λ x, 1 / √ 2 * arccos (√ 2 * x / (x ^ 2 + 1)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_vi : forall c,
  ∫ (λ x, arcsin (√ x)) (0, 1) =
  (λ x, (x - 1 / 2) * arcsin (√ x) + 1 / 2 * √ (x - x ^ 2) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_vii : forall c,
  ∫ (λ x, x / (1 + sin x)) =
  (λ x, x * (sin x - 1) / cos x + log (1 + sin x) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_viii : forall c,
  ∫ (λ x, exp (sin x) * (x * (cos x) ^ 3 - sin x) / (cos x) ^ 2) =
  (λ x, exp (sin x) * (x - 1 / cos x) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_ix : forall c,
  ∫ (λ x, √ (tan x)) =
  (λ x, 1 / √ 2 * arctan ((tan x - 1) / √ (2 * tan x)) + 1 / (2 * √ 2) * log ((tan x - √ (2 * tan x) + 1) / (tan x + √ (2 * tan x) + 1)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_8_x : forall c,
  ∫ (λ x, 1 / (x ^ 6 + 1)) =
  (λ x, 1 / 3 * arctan x + 1 / (4 * √ 3) * log ((x ^ 2 + √ 3 * x + 1) / (x ^ 2 - √ 3 * x + 1)) + 1 / 6 * arctan (2 * x + √ 3) + 1 / 6 * arctan (2 * x - √ 3) + c).
Proof.
  auto_int.
Admitted.