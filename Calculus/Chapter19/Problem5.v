From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_5_i : forall c,
  ∫ (λ x, 1 / (1 + √ (x + 1))) (-1, ∞) =
  (λ x, 2 * √ (x + 1) - 2 * log (1 + √ (x + 1)) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_5_ii : forall c,
  ∫ (λ x, 1 / (1 + exp x)) =
  (λ x, x - log (1 + exp x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_5_iii : forall c,
  ∫ (λ x, 1 / (√ x + x ^^ (1 / 3))) (0, ∞) =
  (λ x, 2 * √ x - 3 * (x ^^ (1 / 3)) + 6 * (x ^^ (1 / 6)) - 6 * log (1 + x ^^ (1 / 6)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_iv : forall c,
  ∫ (λ x, 1 / √ (1 + exp x)) =
  (λ x, log ((√ (1 + exp x) - 1) / (√ (1 + exp x) + 1)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_v : forall c,
  ∫ (λ x, 1 / (2 + tan x)) =
  (λ x, 2 / 5 * x + 1 / 5 * log (2 * cos x + sin x) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_vi : forall c,
  ∫ (λ x, 1 / √ (√ x + 1)) (0, ∞) =
  (λ x, 4 / 3 * ((√ x + 1) ^^ (3 / 2)) - 4 * √ (√ x + 1) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_vii : forall c,
  ∫ (λ x, (4 ^^ x + 1) / (2 ^^ x + 1)) =
  (λ x, (2 ^^ x) / log 2 + x - 2 * log (2 ^^ x + 1) / log 2 + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_viii : forall c,
  ∫ (λ x, exp (√ x)) (0, ∞) =
  (λ x, 2 * √ x * exp (√ x) - 2 * exp (√ x) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_5_ix : forall c,
  ∫ (λ x, √ (1 - x) / (1 - √ x)) (0, 1) =
  (λ x, arcsin (√ x) - 2 * √ (1 - x) - √ (x * (1 - x)) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_5_x : forall c,
  ∫ (λ x, √ ((x - 1) / (x + 1)) * (1 / x ^ 2)) (1, ∞) =
  (λ x, arccos (1 / x) - √ (x ^ 2 - 1) / x + c).
Proof.
  auto_int.
Admitted.