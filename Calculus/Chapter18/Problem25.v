From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_25_i :
  ~ (∃ f, continuous f /\ ∀ x, ∫ 0 x f = exp x).
Proof.
  intros [f [H1 H2]].
  specialize (H2 0).
  rewrite integral_n_n, exp_0 in H2. lra.
Qed.

Lemma lemma_18_25_ii : ∀ f, continuous f ->
  ((∀ x, ∫ 0 (x^2) f = 1 - exp (2 * x^2)) <->
   (∀ t, 0 <= t -> f t = -2 * exp (2 * t))).
Proof.
  intros f H1. split.
  - intros H2 t H3.
    assert (H4 : ∀ y, 0 <= y -> ∫ 0 y f = 1 - exp (2 * y)).
    {
      intros y H4. specialize (H2 (sqrt y)).
      rewrite pow2_sqrt in H2; auto.
    }
    pose proof FTC1 f 0 (t + 1) ltac:(lra)
      ltac:(apply continuous_imp_continuous_on; auto) as H5.
    assert (H6 : ⟦ der ⟧ (λ y, ∫ 0 y f) [0, t + 1] = (λ y, -2 * exp (2 * y))).
    {
      apply derivative_on_eq with (f1 := λ y, 1 - exp (2 * y)).
      - intros y H6. symmetry. apply H4. solve_R.
      - auto_diff.
    }
    apply (derivative_on_unique _ _ _ _ H5 H6 t). solve_R.
  - intros H2 x.
    assert (H3 : ∫ 0 (x^2) f = ∫ 0 (x^2) (λ t, -2 * exp (2 * t))).
    { apply integral_ext; [nra |]. intros t H3. apply H2. solve_R. }
    rewrite H3.
    destruct (Req_dec x 0) as [H4 | H4].
    + subst. replace (0^2) with 0 by lra.
      rewrite integral_n_n, Rmult_0_r, exp_0. lra.
    + replace (1 - exp (2 * x^2)) with
        ((λ t, - exp (2 * t)) (x^2) - (λ t, - exp (2 * t)) 0)
        by (cbn beta; rewrite Rmult_0_r, exp_0; lra).
      apply FTC2 with (g := λ t, - exp (2 * t)); [nra | auto_cont | auto_diff].
Qed.