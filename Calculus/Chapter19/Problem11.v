From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_11_i : ∀ c,
  ∫ (λ x, 1 / √ (1 - x ^ 2)) (-1, 1) =
  (λ x, arcsin x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_11_ii : ∀ c,
  ∫ (λ x, 1 / √ (1 + x ^ 2)) =
  (λ x, log (x + √ (1 + x ^ 2)) + c).
Abort.

Lemma lemma_19_11_iii : ∀ c,
  ∫ (λ x, 1 / √ (x ^ 2 - 1)) (1, ∞) =
  (λ x, log (x + √ (x ^ 2 - 1)) + c).
Abort.

Lemma lemma_19_11_iv : ∀ c,
  ∫ (λ x, 1 / (x * √ (x ^ 2 - 1))) (1, ∞) =
  (λ x, arccos (1 / x) + c).
Abort.

Lemma lemma_19_11_v : ∀ c,
  ∫ (λ x, 1 / (x * √ (1 - x ^ 2))) (0, 1) =
  (λ x, - log ((1 + √ (1 - x ^ 2)) / x) + c).
Abort.

Lemma lemma_19_11_vi : ∀ c,
  ∫ (λ x, 1 / (x * √ (1 + x ^ 2))) (0, ∞) =
  (λ x, - log ((1 + √ (1 + x ^ 2)) / x) + c).
Abort.

Lemma lemma_19_11_vii : ∀ c,
  ∫ (λ x, x ^ 3 * √ (1 - x ^ 2)) (-1, 1) =
  (λ x, 1 / 5 * ((1 - x ^ 2) ^^ (5 / 2)) - 1 / 3 * ((1 - x ^ 2) ^^ (3 / 2)) + c).
Abort.

Lemma lemma_19_11_viii : ∀ c,
  ∫ (λ x, √ (1 - x ^ 2)) (-1, 1) =
  (λ x, 1 / 2 * x * √ (1 - x ^ 2) + 1 / 2 * arcsin x + c).
Abort.

Lemma lemma_19_11_ix : ∀ c,
  ∫ (λ x, √ (1 + x ^ 2)) =
  (λ x, 1 / 2 * x * √ (1 + x ^ 2) + 1 / 2 * log (x + √ (1 + x ^ 2)) + c).
Abort.

Lemma lemma_19_11_x : ∀ c,
  ∫ (λ x, √ (x ^ 2 - 1)) (1, ∞) =
  (λ x, 1 / 2 * x * √ (x ^ 2 - 1) - 1 / 2 * log (x + √ (x ^ 2 - 1)) + c).
Abort.