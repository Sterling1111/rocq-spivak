From Calculus.Chapter15 Require Import Prelude.

Definition sin_deg (x : R) : R := sin (π * x / 180).
Definition cos_deg (x : R) : R := cos (π * x / 180).

Lemma lemma_15_21_a_sin :
  ⟦ der ⟧ sin_deg = (λ x, (π / 180) * cos_deg x).
Proof.
  unfold sin_deg, cos_deg. auto_diff.
Qed.

Lemma lemma_15_21_a_cos :
  ⟦ der ⟧ cos_deg = (λ x, -(π / 180) * sin_deg x).
Proof.
  unfold sin_deg, cos_deg. auto_diff.
Qed.

Lemma lemma_15_21_b_1 :
  ⟦ lim 0 ⟧ (λ x, sin_deg x / x) = π / 180.
Proof.
  pose proof lemma_15_21_a_sin 0 as H1.
  unfold derivative_at, sin_deg, cos_deg in H1 |- *.
  replace (π * 0 / 180) with 0 in H1 by lra.
  rewrite sin_0, cos_0, Rmult_1_r in H1.
  replace (λ h, (sin (π * (0 + h) / 180) - 0) / h) with
    (λ h, sin (π * h / 180) / h) in H1 by
    (extensionality h; replace (0 + h) with h by lra; lra).
  exact H1.
Qed.

Lemma lemma_15_21_b_2 :
  ⟦ lim ∞ ⟧ (λ x, x * sin_deg (1 / x)) = π / 180.
Proof.
  intros ε H1.
  destruct (lemma_15_21_b_1 ε H1) as [δ [H2 H3]].
  exists (1 / δ). intros x H4.
  assert (H5 : 0 < x) by (pose proof Rdiv_pos_pos 1 δ ltac:(lra) H2; lra).
  assert (H6 : 0 < 1 / x < δ) by solve_R.
  specialize (H3 (1 / x) ltac:(solve_R)).
  replace (sin_deg (1 / x) / (1 / x)) with (x * sin_deg (1 / x)) in H3 by (field; lra).
  exact H3.
Qed.
