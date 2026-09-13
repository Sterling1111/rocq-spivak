From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_27_b : ∀ x,
  0 < x < π / 2 ->
  cos x < sin x / x < 1.
Abort.

Lemma lemma_15_27_c :
  ⟦ lim 0 ⟧ (λ x, (1 - cos x) / x) = 0.
Proof.
  apply limit_eq with (f1 := λ x, (sin x / x) * (sin x / (1 + cos x))).
  - exists (π / 2). split; [pose proof π_pos; lra |]. intros x H1.
    assert (H2 : cos x > 0) by (apply cos_gt_0; solve_R).
    pose proof pythagorean_identity x as H3.
    assert (H4 : x <> 0) by solve_R.
    apply Rmult_eq_reg_r with (r := x * (1 + cos x)).
    + field_simplify; nra.
    + apply Rmult_integral_contrapositive; split; lra.
  - replace 0 with (1 * (0 / (1 + 1))) at 2 by lra.
    apply limit_mult; [apply limit_sin_x_over_x |].
    apply limit_div; [apply limit_sin_0 | | lra].
    apply limit_plus; [apply limit_const |].
    replace 1 with (cos 0) by apply cos_0. apply limit_cos.
Qed.

Lemma lemma_15_27_d :
  ⟦ der ⟧ sin = cos.
Proof.
  intro x. unfold derivative_at.
  apply limit_eq with
    (f1 := λ h, cos x * (sin h / h) - sin x * ((1 - cos h) / h)).
  - exists 1. split; [lra |]. intros h H1. rewrite sin_plus. field. solve_R.
  - assert (H1 : ⟦ lim 0 ⟧
      (λ h, cos x * (sin h / h) - sin x * ((1 - cos h) / h)) = cos x * 1 - sin x * 0).
    { apply limit_minus; apply limit_mult; try apply limit_const.
      - apply limit_sin_x_over_x.
      - apply lemma_15_27_c. }
    replace (cos x * 1 - sin x * 0) with (cos x) in H1 by ring. exact H1.
Qed.
