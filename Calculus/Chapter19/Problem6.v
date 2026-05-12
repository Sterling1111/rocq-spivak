From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_6_i : forall c,
  ∫ (λ x, (2 * x ^ 2 + 7 * x - 1) / (x ^ 3 + x ^ 2 - x - 1)) (1, ∞) =
  (λ x, 2 * log (x - 1) - 3 / (x + 1) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_6_ii : forall c,
  ∫ (λ x, (2 * x + 1) / (x ^ 3 - 3 * x ^ 2 + 3 * x - 1)) (1, ∞) =
  (λ x, - 2 / (x - 1) - 3 / (2 * (x - 1) ^ 2) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_6_iii : forall c,
  ∫ (λ x, (x ^ 3 + 7 * x ^ 2 - 5 * x + 5) / ((x - 1) ^ 2 * (x + 1) ^ 3)) (1, ∞) =
  (λ x, - 1 / (x - 1) - 2 / (x + 1) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_6_iv : forall c,
  ∫ (λ x, (2 * x ^ 2 + x + 1) / ((x + 3) * (x - 1) ^ 2)) (1, ∞) =
  (λ x, log (x + 3) + log (x - 1) - 1 / (x - 1) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_6_v : forall c,
  ∫ (λ x, (x + 4) / (x ^ 2 + 1)) =
  (λ x, 1 / 2 * log (x ^ 2 + 1) + 4 * arctan x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_6_vi : forall c,
  ∫ (λ x, (x ^ 3 + x + 2) / (x ^ 4 + 2 * x ^ 2 + 1)) =
  (λ x, 1 / 2 * log (x ^ 2 + 1) + arctan x + x / (x ^ 2 + 1) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_6_vii : forall c,
  ∫ (λ x, (3 * x ^ 2 + 3 * x + 1) / (x ^ 3 + 2 * x ^ 2 + 2 * x + 1)) (-1, ∞) =
  (λ x, log (x + 1) + log (x ^ 2 + x + 1) - 2 / √ 3 * arctan ((2 * x + 1) / √ 3) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_6_viii : forall c,
  ∫ (λ x, 1 / (x ^ 4 + 1)) =
  (λ x, 1 / (4 * √ 2) * log ((x ^ 2 + √ 2 * x + 1) / (x ^ 2 - √ 2 * x + 1)) + 1 / (2 * √ 2) * arctan (√ 2 * x + 1) + 1 / (2 * √ 2) * arctan (√ 2 * x - 1) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_6_ix : forall c,
  ∫ (λ x, 2 * x / ((x ^ 2 + x + 1) ^ 2)) =
  (λ x, - (2 * x + 4) / (3 * (x ^ 2 + x + 1)) - 4 / (3 * √ 3) * arctan ((2 * x + 1) / √ 3) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_6_x : forall c,
  ∫ (λ x, 3 * x / ((x ^ 2 + x + 1) ^ 3)) =
  (λ x, - (x + 2) / (2 * (x ^ 2 + x + 1) ^ 2) - (2 * x + 1) / (2 * (x ^ 2 + x + 1)) - 2 / √ 3 * arctan ((2 * x + 1) / √ 3) + c).
Proof.
  auto_int.
Admitted.