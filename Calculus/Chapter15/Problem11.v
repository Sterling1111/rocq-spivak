From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_11_a : forall m n x,
  sin (m * x) * sin (n * x) = 1/2 * (cos ((m - n) * x) - cos ((m + n) * x)).
Proof.
  intros.
  replace ((m - n) * x) with (m * x - n * x) by lra.
  replace ((m + n) * x) with (m * x + n * x) by lra.
  rewrite cos_minus, cos_plus.
  lra.
Qed.

Lemma lemma_15_11_b : forall m n x,
  sin (m * x) * cos (n * x) = 1/2 * (sin ((m + n) * x) + sin ((m - n) * x)).
Proof.
  intros.
  replace ((m + n) * x) with (m * x + n * x) by lra.
  replace ((m - n) * x) with (m * x - n * x) by lra.
  rewrite sin_plus, sin_minus.
  lra.
Qed.

Lemma lemma_15_11_c : forall m n x,
  cos (m * x) * cos (n * x) = 1/2 * (cos ((m + n) * x) + cos ((m - n) * x)).
Proof.
  intros.
  replace ((m + n) * x) with (m * x + n * x) by lra.
  replace ((m - n) * x) with (m * x - n * x) by lra.
  rewrite cos_plus, cos_minus.
  lra.
Qed.
