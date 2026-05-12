From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_4_i : forall c,
  ∫ (λ x, 1 / √ (1 - x ^ 2)) (-1, 1) =
  (λ x, arcsin x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_4_ii : forall c,
  ∫ (λ x, 1 / √ (1 + x ^ 2)) =
  (λ x, log (x + √ (1 + x ^ 2)) + c).
Proof.
  auto_int.
  
Admitted.

Lemma lemma_19_4_iii : forall c,
  ∫ (λ x, 1 / √ (x ^ 2 - 1)) (1, ∞) =
  (λ x, log (x + √ (x ^ 2 - 1)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_iv : forall c,
  ∫ (λ x, 1 / (x * √ (x ^ 2 - 1))) (1, ∞) =
  (λ x, arccos (1 / x) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_v : forall c,
  ∫ (λ x, 1 / (x * √ (1 - x ^ 2))) (0, 1) =
  (λ x, - log ((1 + √ (1 - x ^ 2)) / x) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_vi : forall c,
  ∫ (λ x, 1 / (x * √ (1 + x ^ 2))) (0, ∞) =
  (λ x, - log ((1 + √ (1 + x ^ 2)) / x) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_vii : forall c,
  ∫ (λ x, x ^ 3 * √ (1 - x ^ 2)) (-1, 1) =
  (λ x, 1 / 5 * ((1 - x ^ 2) ^^ (5 / 2)) - 1 / 3 * ((1 - x ^ 2) ^^ (3 / 2)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_viii : forall c,
  ∫ (λ x, √ (1 - x ^ 2)) (-1, 1) =
  (λ x, 1 / 2 * x * √ (1 - x ^ 2) + 1 / 2 * arcsin x + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_ix : forall c,
  ∫ (λ x, √ (1 + x ^ 2)) =
  (λ x, 1 / 2 * x * √ (1 + x ^ 2) + 1 / 2 * log (x + √ (1 + x ^ 2)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_4_x : forall c,
  ∫ (λ x, √ (x ^ 2 - 1)) (1, ∞) =
  (λ x, 1 / 2 * x * √ (x ^ 2 - 1) - 1 / 2 * log (x + √ (x ^ 2 - 1)) + c).
Proof.
  auto_int.
Admitted.