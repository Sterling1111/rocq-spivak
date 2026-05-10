From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_15_a_sin2 : forall x,
  (sin x)^2 = (1 - cos (2 * x)) / 2.
Proof.
  intros x. rewrite cos_2x_3. lra.
Qed.

Lemma lemma_15_15_a_cos2 : forall x,
  (cos x)^2 = (1 + cos (2 * x)) / 2.
Proof.
  intros x. rewrite cos_2x_2. lra.
Qed.

Lemma lemma_15_15_b_cos_half : forall x,
  0 <= x <= π / 2 ->
  cos (x / 2) = √((1 + cos x) / 2).
Proof.
  intros x H1.
  pose proof (lemma_15_15_a_cos2 (x / 2)) as H2.
  replace (2 * (x / 2)) with x in H2 by lra.
  assert (H3: 0 <= cos (x / 2)).
  { apply cos_sign_q1. lra. }
  apply (f_equal sqrt) in H2.
  replace (cos (x / 2) ^ 2) with (cos (x / 2) * cos (x / 2)) in H2 by lra.
  rewrite sqrt_square in H2; auto.
Qed.

Lemma lemma_15_15_b_sin_half : forall x,
  0 <= x <= π / 2 ->
  sin (x / 2) = √((1 - cos x) / 2).
Proof.
  intros x H1.
  pose proof (lemma_15_15_a_sin2 (x / 2)) as H2.
  replace (2 * (x / 2)) with x in H2 by lra.
  assert (H3: 0 <= sin (x / 2)).
  {
    assert (x = 0 \/ 0 < x) as [H3 | H3] by lra.
    - rewrite H3. replace (0 / 2) with 0 by lra. rewrite sin_0. lra.
    - assert (0 < x / 2 < π) as H4 by lra.
      pose proof (sin_gt_0 (x / 2) H4). lra.
  }
  apply (f_equal sqrt) in H2.
  replace (sin (x / 2) ^ 2) with (sin (x / 2) * sin (x / 2)) in H2 by lra.
  rewrite sqrt_square in H2; auto.
Qed.

Lemma lemma_15_15_c_sin2 : forall a b,
  a < b ->
  ∫ a b (fun x => (sin x)^2) = (b - a) / 2 - (sin (2 * b) - sin (2 * a)) / 4.
Proof.
  intros a b H1. auto_int.
  - pose proof pythagorean_identity x. nra.
  - repeat rewrite sin_2x. nra.
Qed.

Lemma lemma_15_15_c_cos2 : forall a b,
  a < b ->
  ∫ a b (fun x => (cos x)^2) = (b - a) / 2 + (sin (2 * b) - sin (2 * a)) / 4.
Proof.
  intros a b H1. auto_int.
  - pose proof pythagorean_identity x. nra.
  - repeat rewrite sin_2x. nra.
Qed.
