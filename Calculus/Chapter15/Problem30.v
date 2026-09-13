From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_30_a : ∀ y₀ y₀',
  ⟦ der ⟧ y₀ = y₀' ->
  (∀ x, ⟦ der x ⟧ y₀' = (λ x, - y₀ x)) ->
  ∃ c, ∀ x, (y₀ x)^2 + (y₀' x)^2 = c.
Proof.
  intros y₀ y₀' H1 H2.
  apply derivative_zero_imp_const'.
  apply derivative_ext with (f1' := λ x, 2 * y₀ x * y₀' x + 2 * y₀' x * (- y₀ x)).
  - intro x. ring.
  - apply derivative_plus.
    + auto_diff.
    + auto_diff.
Qed.

Lemma lemma_15_30_d : sin (π / 2) = 1.
Proof.
  apply sin_π_over_2.
Qed.

Lemma lemma_15_30_e :
  cos π = -1 /\ sin π = 0 /\ cos (2 * π) = 1 /\ sin (2 * π) = 0.
Proof.
  rewrite cos_π, sin_π, cos_2π, sin_2π. repeat split; reflexivity.
Qed.

Lemma lemma_15_30_f :
  (∀ x, cos (x + 2 * π) = cos x) /\
  (∀ x, sin (x + 2 * π) = sin x).
Proof.
  split; intro x.
  - rewrite cos_plus, cos_2π, sin_2π. lra.
  - rewrite sin_plus, cos_2π, sin_2π. lra.
Qed.
