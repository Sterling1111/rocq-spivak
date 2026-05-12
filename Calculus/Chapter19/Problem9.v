From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_9_i : forall a c, a <> 0 ->
  ∫ (λ x, log (a ^ 2 + x ^ 2)) =
  (λ x, x * log (a ^ 2 + x ^ 2) - 2 * x + 2 * a * arctan (x / a) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_9_ii : forall c,
  ∫ (λ x, (1 + cos x) / (sin x) ^ 2) (0, π) =
  (λ x, - (cos x + 1) / sin x + c).
Proof.
  auto_int.
  pose proof pythagorean_identity x. solve_R.
  pose proof sin_eq_0_on_0_pi x. nra.
Qed.

Lemma lemma_19_9_iii : forall c,
  ∫ (λ x, (x + 1) / √ (4 - x ^ 2)) (-2, 2) =
  (λ x, - √ (4 - x ^ 2) + arcsin (x / 2) + c).
Proof.
  auto_int.
  solve_R.
  - replace (4 - x * x) with (4 * (1 - x / 2 * (x / 2))) by nra.
    rewrite sqrt_mult; [|lra|nra].
    replace (√4) with 2.
    + nra.
    + change 4 with (2 * 2). rewrite sqrt_square; lra.
  - split.
    + apply Rgt_not_eq. apply sqrt_lt_R0. nra.
    + apply Rgt_not_eq. apply sqrt_lt_R0. nra.
Qed.

Lemma lemma_19_9_iv : forall c,
  ∫ (λ x, x * arctan x) =
  (λ x, 1 / 2 * (x ^ 2 + 1) * arctan x - 1 / 2 * x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_9_v : forall c,
  ∫ (λ x, (sin x) ^ 3) =
  (λ x, - cos x + 1 / 3 * (cos x) ^ 3 + c).
Proof.
  auto_int.
  pose proof pythagorean_identity x.
  replace (sin x * sin x) with (1 - cos x * cos x); solve_R.
Qed.

Lemma lemma_19_9_vi : forall c,
  ∫ (λ x, (sin x) ^ 3 / (cos x) ^ 2) (-π / 2, π / 2) =
  (λ x, 1 / cos x + cos x + c).
Proof.
  auto_int.
  pose proof pythagorean_identity x.
  replace (cos x * cos x) with (1 - sin x * sin x); solve_R.
  pose proof cos_gt_0 x; solve_R.
Qed.

Lemma lemma_19_9_vii : forall c,
  ∫ (λ x, x ^ 2 * arctan x) =
  (λ x, 1 / 3 * x ^ 3 * arctan x - 1 / 6 * x ^ 2 + 1 / 6 * log (1 + x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_9_viii : forall c,
  ∫ (λ x, x / √ (x ^ 2 - 2 * x + 2)) =
  (λ x, √ (x ^ 2 - 2 * x + 2) + log (x - 1 + √ (x ^ 2 - 2 * x + 2)) + c).
Proof.
  auto_int.
  - assert (H : x * x - 2 * x + 2 = (x - 1) * (x - 1) + 1) by ring.
    rewrite H.
    destruct (Rle_dec 0 (x - 1)).
    + apply Rplus_le_lt_0_compat; try lra.
      apply sqrt_lt_R0. nra.
    + assert (H0: √((x - 1) * (x - 1) + 1) > -(x - 1)).
      * apply Rsqr_incrst_0; try apply Rle_ge; try apply sqrt_pos; try nra.
        rewrite Rsqr_sqrt; try nra.
        unfold Rsqr. nra.
      * lra.
  - assert (H : x * x - 2 * x + 2 = (x - 1) * (x - 1) + 1) by ring.
    rewrite H.
    destruct (Rle_dec 0 (x - 1)).
    + apply Rgt_not_eq. apply Rplus_le_lt_0_compat; try lra.
      apply sqrt_lt_R0. nra.
    + apply Rgt_not_eq. assert (H0: √((x - 1) * (x - 1) + 1) > -(x - 1)).
      * apply Rsqr_incrst_0; try apply Rle_ge; try apply sqrt_pos; try nra.
        rewrite Rsqr_sqrt; try nra.
        unfold Rsqr. nra.
      * lra.
Qed.

Lemma lemma_19_9_ix : forall c,
  ∫ (λ x, 1 / (cos x) ^ 3 * tan x) (-π / 2, π / 2) =
  (λ x, 1 / (3 * (cos x) ^ 3) + c).
Proof.
  auto_int.
  - apply Rmult_integral_contrapositive; split; try lra.
    apply Rmult_integral_contrapositive; split.
    + apply Rgt_not_eq. apply cos_gt_0. destruct H. lra.
    + apply Rmult_integral_contrapositive; split.
      * apply Rgt_not_eq. apply cos_gt_0. destruct H. lra.
      * apply Rgt_not_eq. apply cos_gt_0. destruct H. lra.
  - unfold tan. solve_R.
    unfold pow in *.
    replace (cos x * (cos x * (cos x * 1))) with (cos x * (cos x * cos x)) in * by ring.
    apply Rgt_not_eq. apply cos_gt_0. destruct H. lra.
Qed.

Lemma lemma_19_9_x : forall c,
  ∫ (λ x, x * (tan x) ^ 2) (-π / 2, π / 2) =
  (λ x, x * tan x + log (cos x) - 1 / 2 * x ^ 2 + c).
Proof.
  auto_int.
  unfold tan.
  pose proof pythagorean_identity x.
  solve_R.
  apply Rgt_not_eq. apply cos_gt_0. lra.
Qed.