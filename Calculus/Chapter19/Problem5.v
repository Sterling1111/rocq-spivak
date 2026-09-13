From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_5_i : ∀ c,
  ∫ (λ x, 1 / (1 + √ (x + 1))) (-1, ∞) =
  (λ x, 2 * √ (x + 1) - 2 * log (1 + √ (x + 1)) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_5_ii : ∀ c,
  ∫ (λ x, 1 / (1 + exp x)) =
  (λ x, x - log (1 + exp x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_5_iii : ∀ c,
  ∫ (λ x, 1 / (√ x + x ^^ (1 / 3))) (0, ∞) =
  (λ x, 2 * √ x - 3 * (x ^^ (1 / 3)) + 6 * (x ^^ (1 / 6)) - 6 * log (1 + x ^^ (1 / 6)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_iv : ∀ c,
  ∫ (λ x, 1 / √ (1 + exp x)) =
  (λ x, log ((√ (1 + exp x) - 1) / (√ (1 + exp x) + 1)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_v : ∀ c,
  ∫ (λ x, 1 / (2 + tan x)) (0, π/2) =
  (λ x, 2 / 5 * x + 1 / 5 * log (2 * cos x + sin x) + c).
Abort.

Lemma lemma_19_5_vi : ∀ c,
  ∫ (λ x, 1 / √ (√ x + 1)) (0, ∞) =
  (λ x, 4 / 3 * ((√ x + 1) ^^ (3 / 2)) - 4 * √ (√ x + 1) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_vii : ∀ c,
  ∫ (λ x, (4 ^^ x + 1) / (2 ^^ x + 1)) =
  (λ x, (2 ^^ x) / log 2 + x - 2 * log (2 ^^ x + 1) / log 2 + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_viii : ∀ c,
  ∫ (λ x, exp (√ x)) (0, ∞) =
  (λ x, 2 * √ x * exp (√ x) - 2 * exp (√ x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_5_ix : ∀ c,
  ∫ (λ x, √ (1 - x) / (1 - √ x)) (0, 1) =
  (λ x, arcsin (√ x) - 2 * √ (1 - x) - √ (x * (1 - x)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_x : ∀ c,
  ∫ (λ x, √ ((x - 1) / (x + 1)) * (1 / x ^ 2)) (1, ∞) =
  (λ x, arccos (1 / x) - √ (x ^ 2 - 1) / x + c).
Proof.
  auto_int.
Admitted.