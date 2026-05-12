From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_10_i : forall a c, a <> 0 ->
  ∫ (λ x, 1 / ((a ^ 2 + x ^ 2) ^ 2)) =
  (λ x, x / (2 * a ^ 2 * (a ^ 2 + x ^ 2)) + 1 / (2 * a ^ 3) * arctan (x / a) + c).
Proof.
  auto_int.
  apply Rmult_integral_contrapositive; split; nra.
Qed.

Lemma lemma_19_10_ii : forall c,
  ∫ (λ x, √ (1 - sin x)) (-π / 2, π / 2) =
  (λ x, 2 * sin (x / 2) + 2 * cos (x / 2) + c).
Proof.
  auto_int.
  assert (2 * (cos (x / 2) * (2 / (2 * 2))) + 2 * (- sin (x / 2) * (2 / (2 * 2))) = cos (x / 2) - sin (x / 2)) as -> by lra.
  symmetry; apply sqrt_lem_1.
  - pose proof (sin_bounds x); lra.
  - assert (Heq : cos (x/2) - sin (x/2) = √2 * cos (x/2 + π/4)).
    { rewrite cos_plus, cos_π_over_4, sin_π_over_4.
      pose proof (sqrt_sqrt 2 (Rlt_le 0 2 ltac:(lra))) as Hsq.
      field_simplify. unfold pow. rewrite Rmult_1_r. rewrite Hsq. lra. }
    rewrite Heq. apply Rmult_le_pos.
    + apply sqrt_pos.
    + apply cos_sign_q1.
      destruct H as [Hl Hr]. pose proof StdlibCompat.π_compat. split; lra.
  - pose proof (sin2_plus_cos2 (x/2)). pose proof (sin_2x (x/2)).
    assert (2 * (x/2) = x) as Hx by lra. rewrite Hx in *. nra.
Qed.

Lemma lemma_19_10_iii : forall c,
  ∫ (λ x, arctan (√ x)) (0, ∞) =
  (λ x, (x + 1) * arctan (√ x) - √ x + c).
Proof.
  auto_int.
  unfold Ensembles.In in H.
  assert (H1 : 0 < √x) by (apply sqrt_lt_R0; lra).
  assert (H2 : √x * √x = x) by (apply sqrt_sqrt; lra).
  assert (H3 : 1 + √x * √x <> 0) by nra.
  assert (H4 : 2 * √x <> 0) by lra.
  field_simplify; [| split; nra].
  assert (√x ^ 2 = x) by (simpl; rewrite Rmult_1_r; lra).
  assert (√x ^ 3 = x * √x) by (simpl; rewrite Rmult_1_r, H2; ring).
  rewrite H0, H5. field. nra.
Qed.

Lemma lemma_19_10_iv : forall c,
  ∫ (λ x, sin (√ (x + 1))) (-1, ∞) =
  (λ x, 2 * sin (√ (x + 1)) - 2 * √ (x + 1) * cos (√ (x + 1)) + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_10_v : forall c,
  ∫ (λ x, √ (x ^ 3 - 2) / x) (2 ^^ (1 / 3), ∞) =
  (λ x, 2 / 3 * √ (x ^ 3 - 2) - 2 * √ 2 / 3 * arctan (√ (x ^ 3 - 2) / √ 2) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_10_vi : forall c,
  ∫ (λ x, log (x + √ (x ^ 2 - 1))) (1, ∞) =
  (λ x, x * log (x + √ (x ^ 2 - 1)) - √ (x ^ 2 - 1) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_10_vii : forall c,
  ∫ (λ x, log (x + √ x)) (0, ∞) =
  (λ x, x * log (x + √ x) - 2 / 3 * (x ^^ (3 / 2)) + 1 / 2 * x - √ x + log (√ x + 1) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_10_viii : forall c,
  ∫ (λ x, 1 / (x - x ^^ (3 / 5))) (1, ∞) =
  (λ x, 5 / 2 * log (x ^^ (2 / 5) - 1) + c).
Proof.
  auto_int.
Admitted.

Lemma lemma_19_10_ix : forall c,
  ∫ (λ x, (arcsin x) ^ 2) (-1, 1) =
  (λ x, x * (arcsin x) ^ 2 + 2 * √ (1 - x ^ 2) * arcsin x - 2 * x + c).
Proof.
  auto_int.
Qed.

Lemma lemma_19_10_x : forall c,
  ∫ (λ x, x ^ 5 * arctan (x ^ 2)) =
  (λ x, 1 / 6 * x ^ 6 * arctan (x ^ 2) - 1 / 12 * x ^ 4 + 1 / 12 * log (1 + x ^ 4) + c).
Proof.
  auto_int.
Qed.