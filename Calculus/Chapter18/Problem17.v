From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_17_a :
   ⟦ lim 0 ⟧ (λ y, log (1 + y) / y) = 1.
Proof.
  pose proof (derivative_log_x 1 ltac:(lra)) as H1.
  unfold derivative_at in H1.
  rewrite log_1 in H1.
  replace (λ h : ℝ, (log (1 + h) - 0) / h)
    with (λ h : ℝ, log (1 + h) / h) in H1
    by (extensionality h; lra).
  replace (1 / 1) with 1 in H1 by lra.
  exact H1.
Qed.

Lemma lemma_18_17_b :
   ⟦ lim ∞ ⟧ (λ x, x * log (1 + 1 / x)) = 1.
Abort.

Lemma lemma_18_17_c :
   ⟦ lim ∞ ⟧ (λ x, exp (x * log (1 + 1 / x))) = e.
Abort.

Lemma lemma_18_17_d : ∀ a,
   ⟦ lim ∞ ⟧ (λ x, exp (x * log (1 + a / x))) = e ^^ a.
Abort.

Lemma lemma_18_17_e : ∀ b,
   b > 0 ->
   ⟦ lim ∞ ⟧ (λ x, x * (b ^^ (1 / x) - 1)) = log b.
Proof.
  intros b H1.
  assert (H2 : ⟦ der 0 ⟧ (λ y, exp (log b * y)) = (λ y, log b * exp (log b * y))) by auto_diff.
  unfold derivative_at in H2.
  replace (log b * 0) with 0 in H2 by lra.
  rewrite exp_0 in H2.
  replace (log b * 1) with (log b) in H2 by lra.
  replace (λ h : ℝ, (exp (log b * (0 + h)) - 1) / h) with
    (λ h : ℝ, (exp (log b * h) - 1) / h) in H2
    by (extensionality h; replace (0 + h) with h by lra; reflexivity).
  intros ε H3.
  destruct (H2 ε H3) as [δ [H4 H5]].
  exists (Rmax 1 (1 / δ)). intros x H6.
  assert (H7 : 0 < x) by solve_R.
  assert (H8 : 0 < 1 / x < δ) by solve_R.
  specialize (H5 (1 / x) ltac:(solve_R)).
  replace (x * (b ^^ (1 / x) - 1)) with
    ((exp (log b * (1 / x)) - 1) / (1 / x)); auto.
  rewrite Rpower_def_pos by lra.
  rewrite Rmult_comm with (r1 := log b).
  solve_R.
Qed.
