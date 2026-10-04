From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_9_i : ∀ a c, a <> 0 ->
  ∫ (λ x, log (a ^ 2 + x ^ 2)) =
  (λ x, x * log (a ^ 2 + x ^ 2) - 2 * x + 2 * a * arctan (x / a) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_9_ii : ∀ c,
  ∫ (λ x, (1 + cos x) / (sin x) ^ 2) (0, π) =
  (λ x, - (cos x + 1) / sin x + c).
Proof.
  auto_int.
  pose proof pythagorean_identity x. solve_R.
  pose proof sin_eq_0_on_0_pi x. solve_R.
Qed.

Lemma lemma_19_9_iii : ∀ c,
  ∫ (λ x, (x + 1) / √ (4 - x ^ 2)) (-2, 2) =
  (λ x, - √ (4 - x ^ 2) + arcsin (x / 2) + c).
Proof.
  auto_int.
  destruct H as [Hlo Hhi].
  assert (Hb : 0 < 1 - x / 2 * (x / 2)) by nra.
  assert (Hs : √(4 - x * x) = 2 * √(1 - x / 2 * (x / 2))).
  { replace (4 - x * x) with (4 * (1 - x / 2 * (x / 2))) by field.
    rewrite sqrt_mult by lra.
    replace (√4) with 2 by (replace 4 with (2 * 2) by ring; rewrite sqrt_square; lra).
    reflexivity. }
  pose proof (sqrt_lt_R0 _ Hb).
  rewrite Hs. field; lra.
Qed.

Lemma lemma_19_9_iv : ∀ c,
  ∫ (λ x, x * arctan x) =
  (λ x, 1 / 2 * (x ^ 2 + 1) * arctan x - 1 / 2 * x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_9_v : ∀ c,
  ∫ (λ x, (sin x) ^ 3) =
  (λ x, - cos x + 1 / 3 * (cos x) ^ 3 + c).
Proof.
  auto_int.
  pose proof pythagorean_identity x.
  replace (sin x * sin x) with (1 - cos x * cos x); solve_R.
Qed.

Lemma lemma_19_9_vi : ∀ c,
  ∫ (λ x, (sin x) ^ 3 / (cos x) ^ 2) (-π / 2, π / 2) =
  (λ x, 1 / cos x + cos x + c).
Proof.
  auto_int.
  pose proof pythagorean_identity x.
  replace (cos x * cos x) with (1 - sin x * sin x); solve_R.
  pose proof cos_gt_0 x; solve_R.
Qed.

Lemma lemma_19_9_vii : ∀ c,
  ∫ (λ x, x ^ 2 * arctan x) =
  (λ x, 1 / 3 * x ^ 3 * arctan x - 1 / 6 * x ^ 2 + 1 / 6 * log (1 + x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_9_viii : ∀ c,
  ∫ (λ x, x / √ (x ^ 2 - 2 * x + 2)) =
  (λ x, √ (x ^ 2 - 2 * x + 2) + log (x - 1 + √ (x ^ 2 - 2 * x + 2)) + c).
Proof. auto_int. Qed.

Lemma lemma_19_9_ix : ∀ c,
  ∫ (λ x, 1 / (cos x) ^ 3 * tan x) (-π / 2, π / 2) =
  (λ x, 1 / (3 * (cos x) ^ 3) + c).
Proof.
  auto_int.
  all: pose proof (cos_gt_0 x ltac:(solve_R)); unfold tan;
    try solve [solve_R]; try field;
    repeat split; repeat apply Rmult_integral_contrapositive_currified; nra.
Qed.

Lemma lemma_19_9_x : ∀ c,
  ∫ (λ x, x * (tan x) ^ 2) (-π / 2, π / 2) =
  (λ x, x * tan x + log (cos x) - 1 / 2 * x ^ 2 + c).
Proof.
  auto_int.
  all: pose proof (cos_gt_0 x ltac:(solve_R));
    pose proof (pythagorean_identity x); unfold tan;
    try solve [solve_R]; field_simplify; nra.
Qed.