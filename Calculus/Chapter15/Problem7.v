From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_7_a_sin2x : forall x,
  sin (2 * x) = 2 * sin x * cos x.
Proof.
  intros x.
  replace (2 * x) with (x + x) by lra.
  rewrite sin_plus.
  lra.
Qed.

Lemma lemma_15_7_a_cos2x : forall x,
  cos (2 * x) = (cos x)^2 - (sin x)^2.
Proof.
  intros x.
  replace (2 * x) with (x + x) by lra.
  rewrite cos_plus.
  lra.
Qed.

Lemma lemma_15_7_a_sin3x : forall x,
  sin (3 * x) = 3 * sin x - 4 * (sin x)^3.
Proof.
  intros x.
  replace (3 * x) with (2 * x + x) by lra.
  rewrite sin_plus.
  rewrite lemma_15_7_a_sin2x.
  rewrite lemma_15_7_a_cos2x.
  pose proof pythagorean_identity x as H1.
  replace (2 * sin x * cos x * cos x) with (2 * sin x * cos x ^ 2) by lra.
  replace (cos x ^ 2) with (1 - sin x ^ 2); nra.
Qed.

Lemma lemma_15_7_a_cos3x : forall x,
  cos (3 * x) = 4 * (cos x)^3 - 3 * cos x.
Proof.
  intros x.
  replace (3 * x) with (2 * x + x) by lra.
  rewrite cos_plus.
  rewrite lemma_15_7_a_cos2x.
  rewrite lemma_15_7_a_sin2x.
  pose proof pythagorean_identity x as H1.
  replace (2 * sin x * cos x * sin x) with (2 * cos x * sin x ^ 2) by lra.
  replace (sin x ^ 2) with (1 - cos x ^ 2) by lra.
  nra.
Qed.

Lemma lemma_15_7_b_sin_pi_4 : sin (π / 4) = √2 / 2.
Proof.
  
Abort.

Lemma lemma_15_7_b_cos_pi_4 : cos (π / 4) = √2 / 2.
Abort.

Lemma lemma_15_7_b_tan_pi_4 : tan (π / 4) = 1.
Abort.

Lemma lemma_15_7_b_sin_pi_6 : sin (π / 6) = 1 / 2.
Abort.

Lemma lemma_15_7_b_cos_pi_6 : cos (π / 6) = √3 / 2.
Abort.
