From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_18_a : ∀ x,
  sin (x + π / 2) = cos x.
Proof.
  intros x. rewrite sin_plus, cos_π_over_2, sin_π_over_2. lra.
Qed.

Lemma lemma_15_18_b_arcsin_sin : ∀ x,
  -π / 2 <= x <= π / 2 ->
  arcsin (sin x) = x.
Proof.
  intros x H1. apply arcsin_spec. split; lra.
Qed.

Lemma lemma_15_18_b_arcsin_cos : ∀ x,
  0 <= x <= π ->
  arcsin (cos x) = π / 2 - x.
Proof.
  intros x H1.
  replace (cos x) with (sin (π / 2 - x)).
  - apply arcsin_spec. split; lra.
  - rewrite sin_minus, sin_π_over_2, cos_π_over_2. lra.
Qed.

Lemma lemma_15_18_b_arccos_sin : ∀ x,
  -π / 2 <= x <= π / 2 ->
  arccos (sin x) = π / 2 - x.
Proof.
  intros x H1.
  replace (sin x) with (cos (π / 2 - x)).
  - apply arccos_spec. split; lra.
  - rewrite cos_minus, sin_π_over_2, cos_π_over_2. lra.
Qed.
